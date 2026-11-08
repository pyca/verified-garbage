module

public import VerifiedGarbage.Proof.Aes.X86_64.Group
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Aes.X86_64.Sse.Layers
import VerifiedGarbage.Proof.Framework.X86_64.Avx

-- separate module: the proof of the groups of eight blocks, which the whole function's
-- (`Ctr32.lean`, whose constant-time check evaluates all the code) need not check again.

/-!
# Eight blocks at a time in SSE2 registers, on x86-64: encryption and a group of counter mode

`encrypt8_ok`: from eight blocks in the quadwords of `xmm0 … xmm7`
(`InRel` in each), with the bitsliced round keys in the scratch buffer
(`EncPre`, as for `encrypt4`), ShiftRows' masks at `r11` and the S-box's
spill slots at `rcx` (`SsePre`), `encrypt8` leaves the eight ciphertexts,
having written only the first 384 bytes of the scratch buffer. The layers
are composed as in `Encrypt.lean`, in each quadword.

`ctrBlocks` builds the counter blocks `c + b` (`b < 8`) from the slots of
the counter block, in quadword `b / 4` of `q (b % 4)` and `q (b % 4 + 4)`
(`ctrBlocks_wp`, then `Group.lean`'s `ctr_inRel` in each quadword, as the
groups `2g` and `2g + 1` of four), `encrypt8` encrypts them, and `xorFull`
or `xorTail` XOR the keystream into the data, 16 bytes at a time. `sseGroup_ok` keeps `Group.lean`'s invariant of
the group loop, `GInv`, from group `g` of four to `g + 2`.
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes
open VG.Proof.Aes.X86_64 (EncPre KeysAt)
open VG.Impl.Aes.X86_64 (at_)
open VG.X86_64.RegUpd (xmm_setXmm_self xmm_setXmm_of_ne)
open VG.X86_64.StraightY (qword_xor qword_app)

/-- What encryption needs besides `EncPre`: the spill slots at `rcx`, the
scratch buffer, and ShiftRows' masks at `r11`, 464 bytes into it. -/
structure SsePre (s₀ : State) : Prop where
  rcx : s₀.gpr .rcx = s₀.gpr .r9
  r11 : s₀.gpr .r11 = s₀.gpr .r9 + BitVec.ofNat 64 srOff
  masks : ∀ k < 2, ∀ l < 2,
    qword (s₀.mem.readW (s₀.gpr .r11 + BitVec.ofNat 64 (16 * k)) 128) l = (srMasks.getD k (0, 0)).2

/-- What stays the same during encryption. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ≠ .rax → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr .r9, 384⟩] s₀.mem s.mem

theorem Ctx.refl (s₀ : State) : Ctx s₀ s₀ := ⟨rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.keeps {s₀ s s' : State} (hc : Ctx s₀ s) (h : Keeps s s') : Ctx s₀ s' :=
  ⟨h.rd.trans hc.rd, h.wr.trans hc.wr, fun r h1 h2 => (h.gpr r h1).trans (hc.keep r h1 h2),
    by rw [h.mem]; exact hc.frame⟩

theorem Ctx.r9 {s₀ s : State} (hc : Ctx s₀ s) : s.gpr .r9 = s₀.gpr .r9 := hc.keep _ (by decide) (by decide)

/-- `Keeps`, with `kp` unchanged. -/
theorem layer_wp {s₀ s : State} {is : List Instr} {P : State → Prop} {Q : State → Prop}
    (hl : ∃ s', runBlock isa is s = some s' ∧ P s' ∧ Keeps s s') (hc : Ctx s₀ s)
    (hQ : ∀ s', Ctx s₀ s' → P s' → s'.gpr kp = s.gpr kp → Q s') : WP isa (.block is) s Q := by
  obtain ⟨s', hs', hP, hk⟩ := hl
  exact WP.of_runBlock ⟨s', hs', hQ s' (hc.keeps hk) hP (hk.gpr kp (by decide))⟩

/-! ## AddRoundKey -/

/-- Word `j` of the bitsliced round key at `kp`. -/
abbrev keyWord (s : State) (j : Nat) : BitVec 64 := s.mem.readW (s.gpr kp + BitVec.ofNat 64 (8 * j)) 64

def arkW (j : Nat) : List Instr := [ldx ta kp (8 * j), bin .punpcklqdq ta ta, pxor (q j) ta]

theorem addRoundKey_eq : addRoundKey = (List.range 8).flatMap arkW := rfl

theorem q_inj : ∀ i < 8, ∀ j < 8, q i = q j → i = j := by decide

theorem q_ne_ta : ∀ i < 8, q i ≠ ta := by decide

theorem q_ne_m' : ∀ i < 8, ∀ k < 6, q i ≠ m (k + 1) := by decide

theorem q_ne_m (i : Nat) (hi : i < 8) (k : Nat) (h1 : 1 ≤ k) (h2 : k < 7) : q i ≠ m k := by
  have := q_ne_m' i hi (k - 1) (by omega)
  rwa [Nat.sub_add_cancel h1] at this

theorem qword_lo_readW (m : Mem) (a : Addr) : qword (m.readW a 128) 0 = m.readW a 64 := by
  have := readW_extract m a (w := 128) (k := 0) (n := 8) (by decide)
  simpa [qword] using this

theorem ldx_step {s : State} {d : XReg} {b : Reg} {o : Nat}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 o) 16) :
    exec (ldx d b o) s = some (s.setXmm d (s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 128)) := by
  have hea : s.ea (at_ b o) = s.gpr b + BitVec.ofNat 64 o := by
    simp only [State.ea, at_]; congr 1
  simp only [ldx, reduceExec, State.load128, hea, hin, ite_true, Option.map_some]

theorem arkW_wp {s : State} {j : Nat} (hj : j < 8)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (8 * j)) 16) {Q : State → Prop}
    (h : ∀ s', (∀ l < 2, QX s' l j = QX s l j ^^^ keyWord s j) →
      (∀ i < 8, i ≠ j → ∀ l, QX s' l i = QX s l i) → Keeps s s' → Q s') :
    WP isa (.block (arkW j)) s Q := by
  refine WP.of_runBlock ⟨_, by
    rw [arkW, runBlock_cons, ldx_step hin, runStep_some, runBlock_cons]
    simp only [bin, reduceExec, XOp.exec, runStep_some]
    rw [runBlock_cons]
    simp only [pxor, bin, reduceExec, XOp.exec, runStep_some, runBlock_nil]
    rfl, h _ ?_ ?_ ?_⟩
  · intro l hl
    simp only [QX, xmm_setXmm_self, XBinOp.eval, qword_xor]
    simp only [xmm_setXmm_of_ne _ _ (q_ne_ta j hj)]
    rw [qword_app _ _ hl, qword_lo_readW]
    split <;> rfl
  · intro i hi hij l
    simp only [QX]
    rw [xmm_setXmm_of_ne _ _ (fun h => hij (q_inj i hi j hj h)), xmm_setXmm_of_ne _ _ (q_ne_ta i hi),
      xmm_setXmm_of_ne _ _ (q_ne_ta i hi)]
  · exact ⟨rfl, rfl, fun _ _ => rfl, rfl⟩

/-- The first `n` words of AddRoundKey. -/
theorem ark_upto : ∀ n ≤ 8, ∀ {s : State},
    (∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (8 * j)) 16) → ∀ {Q : State → Prop},
    (∀ s', (∀ l < 2, ∀ j < 8, QX s' l j = if j < n then QX s l j ^^^ keyWord s j else QX s l j) →
      Keeps s s' → Q s') →
    WP isa (.block ((List.range n).flatMap arkW)) s Q
  | 0, _, s, _, _, h => WP.block_nil (h s (fun _ _ _ _ => by simp) ⟨rfl, rfl, fun _ _ => rfl, rfl⟩)
  | n + 1, hn, s, hin, Q, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff (M := isa)]
    refine ark_upto n (by omega) hin fun s₁ h₁ k₁ => ?_
    have hin₁ : ∀ j < 8, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr kp + BitVec.ofNat 64 (8 * j)) 16 := by
      rw [k₁.rd, k₁.wr, k₁.gpr kp (by decide)]; exact hin
    refine arkW_wp (by omega) (hin₁ n (by omega)) fun s₂ h₂ o₂ k₂ =>
      h s₂ (fun l hl j hj => ?_) (k₁.trans k₂)
    have hk : keyWord s₁ n = keyWord s n := by simp only [keyWord, k₁.mem, k₁.gpr kp (by decide)]
    by_cases hjn : j = n
    · subst hjn; rw [h₂ l hl, h₁ l hl j hj, hk]; simp
    · rw [o₂ j hj hjn l, h₁ l hl j hj]
      by_cases hjl : j < n
      · simp [hjl, show j < n + 1 by omega]
      · simp [hjl, show ¬ j < n + 1 by omega]

theorem addRoundKey_wp {s : State}
    (hin : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (8 * j)) 16) {Q : State → Prop}
    (h : ∀ s', (∀ l < 2, ∀ j < 8, ∀ p < 64,
      (QX s' l j).getLsbD p = ((QX s l j).getLsbD p ^^ (keyWord s j).getLsbD p)) → Keeps s s' → Q s') :
    WP isa (.block addRoundKey) s Q := by
  rw [addRoundKey_eq]
  exact ark_upto 8 (Nat.le_refl _) hin fun s' h' k' =>
    h s' (fun l hl j hj p _ => by rw [h' l hl j hj]; simp [hj]) k'

/-! ## The layers, keeping `Ctx` -/

section
variable {s₀ : State} {R : Nat} {w : List Byte}

/-- The scratch buffer. -/
abbrev scr (s₀ : State) : Region := ⟨s₀.gpr .r9, 2048⟩

theorem Ctx.scr {s : State} (hp : EncPre s₀ R w) (hc : Ctx s₀ s) : scr s₀ ∈ s.wr := by
  rw [hc.wr]; exact hp.scr

theorem sbox_wp {s : State} (hp : EncPre s₀ R w) (hq : SsePre s₀) (hc : Ctx s₀ s) {Q : State → Prop}
    (h : ∀ s', Ctx s₀ s' → (∀ l < 2, ∀ j < 8, ∀ p < 64,
      (QX s' l j).getLsbD p = (Spec.Aes.sbox (bsByte (QX s l) p)).getLsbD j) → s'.gpr kp = s.gpr kp →
      Q s') :
    WP isa (.block sboxCode) s Q := by
  have hrcx : s.gpr .rcx = s₀.gpr .r9 + BitVec.ofNat 64 0 := by
    rw [hc.keep _ (by decide) (by decide), hq.rcx]; simp
  have hok : Ok sboxCfg s := Ok.of_off (hc.scr hp) hrcx (by simp [sboxCfg, spills]) (by simp)
  obtain ⟨s', hs', hbits, hrd, hwr, -, -, hgpr, -, hfr⟩ := sbox_ok hok
  refine WP.of_runBlock ⟨s', hs', h s' ⟨hrd.trans hc.rd, hwr.trans hc.wr,
    fun r h1 h2 => (hgpr r h1).trans (hc.keep r h1 h2), hc.frame.trans (hfr.sub fun r hr => ?_)⟩ hbits
    (hgpr kp (by decide))⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [slotRegion, sboxCfg, spills, hrcx, BitVec.add_zero]
  exact Region.sub_prefix (by omega)

/-- The masks are where `SsePre` put them. -/
theorem masks_at {s : State} (hq : SsePre s₀) (hc : Ctx s₀ s) {k : Nat} (hk : k < 2) :
    s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (16 * k)) 128 =
      s₀.mem.readW (s₀.gpr .r11 + BitVec.ofNat 64 (16 * k)) 128 := by
  rw [hc.keep _ (by decide) (by decide), hq.r11, Offset.add_add]
  refine hc.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact (Offset.base_disjoint _ (by simp [srOff]; omega) (by simp [srOff]; omega)).symm

theorem shiftRows_wp {s : State} (hp : EncPre s₀ R w) (hq : SsePre s₀) (hc : Ctx s₀ s)
    {Q : State → Prop}
    (h : ∀ s', Ctx s₀ s' → (∀ l < 2, ∀ j < 8, ∀ p < 64,
      (QX s' l j).getLsbD p = (QX s l j).getLsbD (srSrc p)) → s'.gpr kp = s.gpr kp → Q s') :
    WP isa (.block shiftRows) s Q := by
  have hin : ∀ k < 2, InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 (16 * k)) 16 := by
    intro k hk
    refine ⟨scr s₀, List.mem_append_right _ (hc.scr hp), ?_⟩
    rw [hc.keep _ (by decide) (by decide), hq.r11, Offset.add_add]
    exact Offset.contains_base _ (by simp [srOff]; omega) (by simp [srOff]; omega)
  have hin₁ : InRegions ((s.setXmm (m 1) (s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (16 * 0)) 128)).rd ++
      (s.setXmm (m 1) (s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (16 * 0)) 128)).wr)
      ((s.setXmm (m 1) (s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (16 * 0)) 128)).gpr .r11 +
        BitVec.ofNat 64 16) 16 := hin 1 (by decide)
  rw [shiftRows, WP.block_append_iff (M := isa)]
  refine WP.of_runBlock ⟨_, by
    rw [srLoad, runBlock_cons, ldx_step (hin 0 (by decide)), runStep_some, runBlock_cons, ldx_step hin₁,
      runStep_some, runBlock_nil], ?_⟩
  have hm : ∀ k < 2, ∀ l < 2, qword (((s.setXmm (m 1) (s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (16 * 0)) 128)).setXmm
      (m 2) (s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 16) 128)).xmm (m (1 + k))) l =
      (srMasks.getD k (0, 0)).2 := by
    intro k hk l hl
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · rw [xmm_setXmm_of_ne _ _ (by decide), xmm_setXmm_self, masks_at hq hc (by decide), hq.masks 0 (by decide) l hl]
    · rw [xmm_setXmm_self, show (16 : Nat) = 16 * 1 from rfl, masks_at hq hc (by decide),
        hq.masks 1 (by decide) l hl]
  obtain ⟨s', hs', hbits, hk⟩ := srBody_ok hm
  refine WP.of_runBlock ⟨s', hs', h s' (hc.keeps ⟨hk.rd, hk.wr, hk.gpr, hk.mem⟩) (fun l hl j hj p hp => ?_)
    (hk.gpr kp (by decide))⟩
  rw [hbits l hl j hj p hp, QX, xmm_setXmm_of_ne _ _ (q_ne_m j hj 2 (by decide) (by decide)),
    xmm_setXmm_of_ne _ _ (q_ne_m j hj 1 (by decide) (by decide))]


theorem mixColumns_wp {s : State} (hc : Ctx s₀ s) {Q : State → Prop}
    (h : ∀ s', Ctx s₀ s' → (∀ l < 2, ∀ j < 8, ∀ p < 64,
      (QX s' l j).getLsbD p = termsXor (QX s l) (mcTerms j p)) → s'.gpr kp = s.gpr kp → Q s') :
    WP isa (.block mixColumns) s Q :=
  layer_wp (mixColumns_ok s) hc h

/-- `add kp, 64`. -/
theorem addKp_wp {s : State} (hc : Ctx s₀ s) {Q : State → Prop}
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp + (64 : BitVec 32).signExtend 64 →
      (∀ l i, QX s' l i = QX s l i) → Q s') :
    WP isa (.block [.alu .add kp (.imm 64)]) s Q := by
  refine WP.of_runBlock ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, execAlu,
    readSrc, Option.bind_some]; rfl, h _ ?_ ?_ ?_⟩
  · refine ⟨hc.rd, hc.wr, fun r h1 h2 => ?_, hc.frame⟩
    simp only [State.setReg, arithFlags, State.setFlags, h2, ite_false]; exact hc.keep r h1 h2
  · simp [State.setReg]
  · intro l i; simp [QX, State.setReg, arithFlags, State.setFlags]

/-- `mov kp, rdi`. -/
theorem movKp_wp {s : State} (hc : Ctx s₀ s) {Q : State → Prop}
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr .rdi → (∀ l i, QX s' l i = QX s l i) → Q s') :
    WP isa (.block [.mov kp (.reg .rdi)]) s Q := by
  refine WP.of_runBlock ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec,
    readSrc, Option.map_some]; rfl, h _ ?_ ?_ ?_⟩
  · refine ⟨hc.rd, hc.wr, fun r h1 h2 => ?_, hc.frame⟩
    simp only [State.setReg, h2, ite_false]; exact hc.keep r h1 h2
  · simp [State.setReg]
  · intro l i; simp [QX, State.setReg]

open VG.Impl.Aes.X86_64 (lastKey sb) in
/-- `mov rax, r9; add rax, lastKey - 64; cmp kp, rax`. -/
theorem cmpLast_wp {s : State} (hc : Ctx s₀ s) {Q : State → Prop}
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp → (∀ l i, QX s' l i = QX s l i) →
      s'.zf = some (s.gpr kp - (s.gpr sb + (BitVec.ofNat 32 (lastKey - 64)).signExtend 64) == 0) →
      Q s') :
    WP isa (.block [.mov .rax (.reg sb), .alu .add .rax (.imm (BitVec.ofNat 32 (lastKey - 64))),
      .alu .cmp kp (.reg .rax)]) s Q := by
  refine WP.of_runBlock ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec,
    execAlu, readSrc, Option.bind_some, Option.map_some]; rfl, h _ ?_ ?_ ?_ ?_⟩
  · refine ⟨hc.rd, hc.wr, fun r h1 h2 => ?_, hc.frame⟩
    simp only [State.setReg, arithFlags, State.setFlags, h1, ite_false]; exact hc.keep r h1 h2
  · simp [State.setReg, arithFlags, State.setFlags, kp]
  · intro l i; simp [QX, State.setReg, arithFlags, State.setFlags]
  · simp [State.setReg, arithFlags, State.setFlags, kp, sb]

/-! ## The round keys -/

open VG.Proof.Aes.X86_64 (keyRel_congr key_contains keys_disjoint kp_off)

theorem keysAt {s : State} (hp : EncPre s₀ R w) (hc : Ctx s₀ s) : KeysAt s.mem (s₀.gpr .rdi) R w := by
  intro j hj
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  refine keyRel_congr (hp.keys j hj) fun k hk => ?_
  rw [hp.k0]
  exact hc.frame.readW (key_contains _ hR hj hk)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact keys_disjoint _) (by decide)

theorem ark_step {s : State} {j : Nat} {T : Nat → Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hc : Ctx s₀ s) (hk : s.gpr kp = s₀.gpr .rdi + BitVec.ofNat 64 (64 * j))
    (hj : j ≤ R) (hbs : ∀ l < 2, BsRel (QX s l) (T l)) {P : State → Prop}
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp →
      (∀ l < 2, BsRel (QX s' l) (fun b => Spec.Aes.addRoundKey (T l b) (Spec.Aes.roundKey w j))) → P s') :
    WP isa (.block addRoundKey) s P := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  have hin : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (8 * i)) 16 := by
    intro i hi
    refine ⟨scr s₀, List.mem_append_right _ (hc.scr hp), ?_⟩
    rw [hk, kp_off _ _ hp.k0, Offset.add_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hkey : VG.Proof.Aes.KeyRel (keyWord s) (Spec.Aes.roundKey w j) := by
    have := keysAt hp hc j hj
    unfold keyWord; rw [hk]; exact this
  exact addRoundKey_wp hin fun s' h' k' => h s' (hc.keeps k') (k'.gpr kp (by decide))
    fun l hl => bs_addRoundKey (h' l hl) (hbs l hl) hkey

end


/-! ## The rounds -/

section
variable {s₀ : State} {R : Nat} {w : List Byte}

open VG.Proof.Aes.X86_64 (rnd midRounds midRounds_succ kp_step zf_last kp_off cipher_eq)
open VG.Impl.Aes.X86_64 (sb)

theorem lanes_eq {s s' : State} (h : ∀ l i, QX s' l i = QX s l i) {T : Nat → Nat → Spec.Aes.State}
    (hbs : ∀ l < 2, BsRel (QX s l) (T l)) : ∀ l < 2, BsRel (QX s' l) (T l) := fun l hl => by
  have : QX s' l = QX s l := funext (h l)
  rw [this]; exact hbs l hl

/-- A middle round. -/
theorem round_ok {s : State} {m : Nat} {T : Nat → Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hq : SsePre s₀) (hc : Ctx s₀ s)
    (hk : s.gpr kp = s₀.gpr .rdi + BitVec.ofNat 64 (64 * m)) (hm : m + 1 < R)
    (hbs : ∀ l < 2, BsRel (QX s l) (T l)) :
    WP isa (.block roundBody) s fun s' => Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr .rdi + BitVec.ofNat 64 (64 * (m + 1)) ∧
      (∀ l < 2, BsRel (QX s' l) (fun b => rnd w (m + 1) (T l b))) ∧ s'.zf = some (decide (m + 2 = R)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  simp only [roundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, kp_step] at hk₁
  have hbs₁ := lanes_eq hq₁ hbs
  refine sbox_wp hp hq hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := fun l hl => bs_subBytes (h₂ l hl) (hbs₁ l hl)
  refine shiftRows_wp hp hq hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := fun l hl => bs_shiftRows (h₃ l hl) (hbs₂ l hl)
  refine mixColumns_wp hc₃ fun s₄ hc₄ h₄ hk₄ => ?_
  have hbs₄ := fun l hl => bs_mixColumns (h₄ l hl) (hbs₃ l hl)
  have hk₄' : s₄.gpr kp = s₀.gpr .rdi + BitVec.ofNat 64 (64 * (m + 1)) := by rw [hk₄, hk₃, hk₂, hk₁]
  refine ark_step hp hc₄ hk₄' (by omega_arith) hbs₄ fun s₅ hc₅ hk₅ hbs₅ => ?_
  refine cmpLast_wp hc₅ fun s₆ hc₆ hk₆ hq₆ hz₆ => ⟨hc₆, by rw [hk₆, hk₅, hk₄'], lanes_eq hq₆ hbs₅, ?_⟩
  rw [hz₆, hk₅, hk₄', hc₅.keep sb (by decide) (by decide), kp_off _ _ hp.k0, zf_last _ hR hm]

/-- Eight blocks, from `InRel` in each quadword to `InRel` of their encryptions. -/
theorem encrypt8_ok {S : Nat → Nat → Spec.Aes.State} (hp : EncPre s₀ R w) (hq : SsePre s₀)
    (hin : ∀ l < 2, InRel (QX s₀ l) (S l)) :
    WP isa encrypt8 s₀ fun s => Ctx s₀ s ∧
      ∀ l < 2, InRel (QX s l) (fun b => Spec.Aes.cipher R w (S l b)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega_arith
  let A : Nat → Nat → Spec.Aes.State := fun l b => Spec.Aes.addRoundKey (S l b) (Spec.Aes.roundKey w 0)
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ Ctx s₀ s ∧
    s.gpr kp = s₀.gpr .rdi + BitVec.ofNat 64 (64 * m) ∧
    ∀ l < 2, BsRel (QX s l) (fun b => midRounds w m (A l b))
  let Mid : State → Prop := fun s => Ctx s₀ s ∧
    s.gpr kp = s₀.gpr .rdi + BitVec.ofNat 64 (64 * (R - 1)) ∧
    ∀ l < 2, BsRel (QX s l) (fun b => midRounds w (R - 1) (A l b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- toBs, the first round key.
    repeat rw [WP.block_append_iff (M := isa)]
    refine layer_wp (toBs_ok s₀) (Ctx.refl s₀) fun s₁ hc₁ h₁ _ => ?_
    have hbs₁ := fun l hl => bs_of_in (h₁ l hl) (hin l hl)
    refine movKp_wp hc₁ fun s₂ hc₂ hk₂ hq₂ => ?_
    have hbs₂ := lanes_eq hq₂ hbs₁
    have hk₂' : s₂.gpr kp = s₀.gpr .rdi + BitVec.ofNat 64 (64 * 0) := by
      rw [hk₂, hc₁.keep _ (by decide) (by decide)]; simp
    exact ark_step hp hc₂ hk₂' (by omega_arith) hbs₂ fun s₃ hc₃ hk₃ hbs₃ =>
      ⟨0, by omega_arith, by omega_arith, hc₃, by rw [hk₃, hk₂'], hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hbs⟩ := hs
    refine WP.mono (round_ok hp hq hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
    by_cases hlast : m + 2 = R
    · refine .inl ⟨by simp [X86_64.eval, hz, hlast], hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega_arith
      · rw [show R - 1 = m + 1 by omega_arith]
        intro l hl b hb i hi
        rw [hbs' l hl b hb i hi]; simp only [midRounds_succ]
    · refine .inr ⟨by simp [X86_64.eval, hz, hlast], R - 1 - (m + 1), by omega_arith, m + 1, rfl,
        by omega_arith, hc', hk', fun l hl b hb i hi => by rw [hbs' l hl b hb i hi]; simp only [midRounds_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [lastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
    rw [hk, kp_step, show R - 1 + 1 = R by omega_arith] at hk₁
    have hbs₁ := lanes_eq hq₁ hbs
    refine sbox_wp hp hq hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
    have hbs₂ := fun l hl => bs_subBytes (h₂ l hl) (hbs₁ l hl)
    refine shiftRows_wp hp hq hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
    have hbs₃ := fun l hl => bs_shiftRows (h₃ l hl) (hbs₂ l hl)
    refine ark_step hp hc₃ (by rw [hk₃, hk₂, hk₁]) (Nat.le_refl R) hbs₃ fun s₄ hc₄ _ hbs₄ => ?_
    refine layer_wp (fromBs_ok s₄) hc₄ fun s₅ hc₅ h₅ _ => ⟨hc₅, fun l hl => ?_⟩
    have := in_of_bs (h₅ l hl) (hbs₄ l hl)
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [cipher_eq]; rfl

end

end VG.Proof.Aes.X86_64.Sse

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes
open VG.Proof.Aes.X86_64 (cloW chiW numW hiWord in_off ofInt_nat)
open VG.Impl.Aes.X86_64 (sb slotAt cLo cHi cNum at_)
open VG.X86_64.RegUpd (xmm_setXmm_self xmm_setXmm_of_ne)

/-! ## The counter words -/

theorem ctrWord_ok {s : State} {b : Addr} {r : Reg} (i : Nat) (hr : r ≠ sb) (hb : s.gpr sb = b)
    (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) :
    ∃ s', runBlock isa (ctrWord r i) s = some s' ∧
      s'.gpr r = hiWord (chiW s.mem b) (numW s.mem b) i ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm := by
  have hw' : (⟨b, 2048⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_right _ hw
  have i440 := in_off hw' (off := 8 * 55) (n := 8) (by omega_arith) (by omega_arith)
  have i448 := in_off hw' (off := 8 * 56) (n := 4) (by omega_arith) (by omega_arith)
  refine ⟨_, by
    simp only [ctrWord, show 1 ≤ 32 ∧ 32 ≤ 63 by decide, and_self, ↓reduceIte, Nat.reduceMul, slotAt, cHi, cNum,
      runBlock_cons, runStep_some, runBlock_nil, reduceExec, execAlu, execAlu32, execShift, readSrc,
      readSrc32, State.load64, State.load32, State.ea, ofInt_nat, State.setReg32, State.setReg,
      State.setFlags, arithFlags, hb, Ne.symm hr,
      i440, i448, Option.map_some, Option.bind_some,
      VG.X86_64.RegUpd.setWidth_setWidth_32]
    rfl, ?_⟩
  refine ⟨?_, fun r' h => by simp [h], rfl, rfl, rfl, rfl⟩
  simp only [hiWord, chiW, numW, ite_true]
  exact BitVec.xor_comm _ _


/-! ## The counter blocks -/

open VG.X86_64.StraightY (qword_app)

def ctrLo : List Instr :=
  [.mov .rax (.mem (slotAt sb cLo)), .xop (.movq (q 0) .rax), bin .punpcklqdq (q 0) (q 0),
   mova (q 1) (q 0), mova (q 2) (q 0), mova (q 3) (q 0)]

def ctrPair (b : Nat) : List Instr :=
  ctrWord .rax b ++ ctrWord .r10 (b + 4) ++
    [.xop (.movq (q (b + 4)) .rax), .xop (.movq ta .r10), bin .punpcklqdq (q (b + 4)) ta]

def ctrNext : List Instr :=
  [.mov32 .rax (.mem (slotAt sb cNum)), .alu32 .add .rax (.imm 8), .store32 (slotAt sb cNum) .rax]

theorem ctrBlocks_eq : ctrBlocks = ctrLo ++ ctrPair 0 ++ ctrPair 1 ++ ctrPair 2 ++ ctrPair 3 ++ ctrNext := by
  simp only [ctrBlocks, ctrLo, ctrPair, ctrNext, List.append_assoc]; rfl

theorem qword_dup (v : BitVec 64) {l : Nat} (hl : l < 2) :
    qword (qword ((0 : BitVec 64) ++ v) 0 ++ qword ((0 : BitVec 64) ++ v) 0) l = v := by
  rw [qword_app _ _ hl, qword_app _ _ (by decide)]; split <;> rfl

theorem ctrLo_ok {s : State} {b : Addr} (hb : s.gpr sb = b) (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) :
    ∃ s', runBlock isa ctrLo s = some s' ∧ (∀ c < 4, ∀ l < 2, QX s' l c = cloW s.mem b) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i432 := in_off (List.mem_append_right s.rd hw) (off := 8 * 54) (n := 8) (by omega_arith) (by omega_arith)
  refine ⟨_, by
    simp only [ctrLo, slotAt, cLo, runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc,
      State.load64, State.ea, ofInt_nat, hb, i432, ite_true, Option.map_some, XOp.exec, bin, mova]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · intro r hr; simp only [VG.X86_64.RegUpd.gpr_setXmm]; simp [State.setReg, hr]
  · rfl
  · rfl
  · rfl
  intro c hc l hl
  have hv : (s.setReg .rax (s.mem.readW (b + BitVec.ofNat 64 (8 * 54)) 64)).gpr .rax =
      s.mem.readW (b + BitVec.ofNat 64 (8 * 54)) 64 := by simp [State.setReg]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [QX, xmm_setXmm_self, XBinOp.eval]
    repeat rw [xmm_setXmm_of_ne _ _ (by decide)]
    repeat rw [xmm_setXmm_self]
    simp only [hv]
    exact qword_dup _ hl


theorem q_ne_ta' : ∀ i < 8, q i ≠ ta := by decide
theorem q_inj' : ∀ i < 8, ∀ j < 8, q i = q j → i = j := by decide

theorem ctrPair_wp {s : State} {b : Addr} {i : Nat} (hi : i < 4) (hb : s.gpr sb = b)
    (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) {P : State → Prop}
    (h : ∀ s', (∀ l < 2, QX s' l (i + 4) = hiWord (chiW s.mem b) (numW s.mem b) (i + 4 * l)) →
      (∀ j < 8, j ≠ i + 4 → ∀ l, QX s' l j = QX s l j) →
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      P s') :
    WP isa (.block (ctrPair i)) s P := by
  rw [ctrPair, WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  obtain ⟨s₁, h₁, a₁, o₁, m₁, rd₁, wr₁, x₁⟩ := ctrWord_ok (r := .rax) i (by decide) hb hw
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  obtain ⟨s₂, h₂, a₂, o₂, m₂, rd₂, wr₂, x₂⟩ := ctrWord_ok (r := .r10) (i + 4) (by decide)
    ((o₁ sb (by decide)).trans hb) (wr₁ ▸ hw)
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  have hne := q_ne_ta' (i + 4) (by omega)
  refine WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, reduceExec, XOp.exec, runStep_some, runBlock_nil, bin]; rfl,
    h _ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro l hl
    simp only [QX, xmm_setXmm_self, XBinOp.eval, xmm_setXmm_of_ne _ _ hne]
    rw [qword_app _ _ hl]
    have e1 : s₂.gpr .rax = hiWord (chiW s.mem b) (numW s.mem b) i := by rw [o₂ _ (by decide), a₁]
    have e2 : s₂.gpr .r10 = hiWord (chiW s.mem b) (numW s.mem b) (i + 4) := by rw [a₂, m₁]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true, qword_app _ _ (show 0 < 2 by decide), e1, Nat.mul_zero, Nat.add_zero]
    · simp only [show ¬ (1 = 0) by decide, ite_false, qword_app _ _ (show 0 < 2 by decide), ite_true,
        VG.X86_64.RegUpd.gpr_setXmm, e2]
  · intro j hj hji l
    have h1 : q j ≠ q (i + 4) := fun h => hji (q_inj' j hj (i + 4) (by omega) h)
    simp only [QX]
    rw [xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ (q_ne_ta' j hj), xmm_setXmm_of_ne _ _ h1, x₂, x₁]
  · intro r h1 h2
    simp only [VG.X86_64.RegUpd.gpr_setXmm]
    rw [o₂ r h2, o₁ r h1]
  · simp only [VG.X86_64.RegUpd.mem_setXmm, m₂, m₁]
  · simp only [VG.X86_64.RegUpd.rd_setXmm, rd₂, rd₁]
  · simp only [VG.X86_64.RegUpd.wr_setXmm, wr₂, wr₁]


/-- `c := c + 8`. -/
theorem ctrNext_ok {s : State} {b : Addr} (hb : s.gpr sb = b) (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) :
    ∃ s', runBlock isa ctrNext s = some s' ∧
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (8 * 56)) (numW s.mem b + 8) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm := by
  have i448 := in_off (List.mem_append_right s.rd hw) (off := 8 * 56) (n := 4) (by omega_arith) (by omega_arith)
  have o448 := in_off hw (off := 8 * 56) (n := 4) (by omega_arith) (by omega_arith)
  refine ⟨_, by
    simp only [ctrNext, show ¬ (sb = Reg.rax) by decide, ↓reduceIte, Nat.reduceMul, slotAt, cNum, runBlock_cons, runStep_some, runBlock_nil,
      reduceExec, execAlu32, readSrc32, State.load32, State.store32, State.ea, ofInt_nat, State.setReg32,
      State.setReg, State.setFlags, arithFlags, hb, i448, o448,
      Option.map_some, Option.bind_some, VG.X86_64.RegUpd.setWidth_setWidth_32]
    rfl, ?_⟩
  exact ⟨rfl, fun r hr => by simp [hr], rfl, rfl, rfl⟩

/-- The eight counter blocks. -/
theorem ctrBlocks_wp {s : State} {b : Addr} (hb : s.gpr sb = b) (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) :
    WP isa (.block ctrBlocks) s fun s' =>
      (∀ c < 4, ∀ l < 2, QX s' l c = cloW s.mem b ∧
        QX s' l (c + 4) = hiWord (chiW s.mem b) (numW s.mem b) (c + 4 * l)) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (8 * 56)) (numW s.mem b + 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [ctrBlocks_eq]
  repeat rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₀, h₀, lo₀, o₀, m₀, rd₀, wr₀⟩ := ctrLo_ok hb hw
  refine WP.of_runBlock ⟨s₀, h₀, ?_⟩
  have hb₀ : s₀.gpr sb = b := (o₀ sb (by decide)).trans hb
  refine ctrPair_wp (i := 0) (by decide) hb₀ (wr₀ ▸ hw) fun s₁ a₁ k₁ o₁ m₁ rd₁ wr₁ => ?_
  have hb₁ : s₁.gpr sb = b := (o₁ sb (by decide) (by decide)).trans hb₀
  refine ctrPair_wp (i := 1) (by decide) hb₁ (wr₁ ▸ wr₀ ▸ hw) fun s₂ a₂ k₂ o₂ m₂ rd₂ wr₂ => ?_
  have hb₂ : s₂.gpr sb = b := (o₂ sb (by decide) (by decide)).trans hb₁
  refine ctrPair_wp (i := 2) (by decide) hb₂ (wr₂ ▸ wr₁ ▸ wr₀ ▸ hw) fun s₃ a₃ k₃ o₃ m₃ rd₃ wr₃ => ?_
  have hb₃ : s₃.gpr sb = b := (o₃ sb (by decide) (by decide)).trans hb₂
  refine ctrPair_wp (i := 3) (by decide) hb₃ (wr₃ ▸ wr₂ ▸ wr₁ ▸ wr₀ ▸ hw) fun s₄ a₄ k₄ o₄ m₄ rd₄ wr₄ => ?_
  have hb₄ : s₄.gpr sb = b := (o₄ sb (by decide) (by decide)).trans hb₃
  obtain ⟨s₅, h₅, m₅, o₅, rd₅, wr₅, x₅⟩ := ctrNext_ok hb₄ (wr₄ ▸ wr₃ ▸ wr₂ ▸ wr₁ ▸ wr₀ ▸ hw)
  have mm : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁, m₀]
  refine WP.of_runBlock ⟨s₅, h₅, fun c hc l hl => ?_, fun r h1 h2 => ?_, by rw [m₅, mm], ?_, ?_⟩
  · have e : QX s₅ l = QX s₄ l := funext fun i => by simp only [QX]; rw [x₅]
    rw [e]
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · rw [k₄ 0 (by decide) (by decide) l, k₃ 0 (by decide) (by decide) l, k₂ 0 (by decide) (by decide) l,
          k₁ 0 (by decide) (by decide) l, lo₀ 0 (by decide) l hl]
      · rw [k₄ 4 (by decide) (by decide) l, k₃ 4 (by decide) (by decide) l, k₂ 4 (by decide) (by decide) l,
          a₁ l hl, m₀]
    · refine ⟨?_, ?_⟩
      · rw [k₄ 1 (by decide) (by decide) l, k₃ 1 (by decide) (by decide) l, k₂ 1 (by decide) (by decide) l,
          k₁ 1 (by decide) (by decide) l, lo₀ 1 (by decide) l hl]
      · rw [k₄ 5 (by decide) (by decide) l, k₃ 5 (by decide) (by decide) l, a₂ l hl, m₁, m₀]
    · refine ⟨?_, ?_⟩
      · rw [k₄ 2 (by decide) (by decide) l, k₃ 2 (by decide) (by decide) l, k₂ 2 (by decide) (by decide) l,
          k₁ 2 (by decide) (by decide) l, lo₀ 2 (by decide) l hl]
      · rw [k₄ 6 (by decide) (by decide) l, a₃ l hl, m₂, m₁, m₀]
    · refine ⟨?_, ?_⟩
      · rw [k₄ 3 (by decide) (by decide) l, k₃ 3 (by decide) (by decide) l, k₂ 3 (by decide) (by decide) l,
          k₁ 3 (by decide) (by decide) l, lo₀ 3 (by decide) l hl]
      · rw [a₄ l hl, m₃, m₂, m₁, m₀]
  · rw [o₅ r h1, o₄ r h1 h2, o₃ r h1 h2, o₂ r h1 h2, o₁ r h1 h2, o₀ r h1]
  · rw [rd₅, rd₄, rd₃, rd₂, rd₁, rd₀]
  · rw [wr₅, wr₄, wr₃, wr₂, wr₁, wr₀]


/-! ## XOR into the data -/

open VG.Proof.Aes.X86_64 (DataInv SrcInv SrcDst SrcDst.far off_toNat add_ofNat_add keyStream ks_of_inRel)
open VG.Proof.Aes (ctrState)

/-- XOR `v` into the 16 bytes at `a`, stored to the 16 bytes at `d`. -/
def xorXTo (m : Mem) (a d : Addr) (v : BitVec 128) : Mem := m.writeW d (m.readW a 128 ^^^ v)

theorem xorXTo_apply (m : Mem) (a d x : Addr) (v : BitVec 128) :
    xorXTo m a d v x =
      if (x - d).toNat < 16 then m (a + (x - d)) ^^^ v.extractLsb' (8 * (x - d).toNat) 8 else m x := by
  unfold xorXTo Mem.writeW Mem.write
  split
  · rename_i h
    have hx : a + BitVec.ofNat 64 (x - d).toNat = a + (x - d) := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have := Mem.extractLsb'_read m a (n := 16) h
    rw [hx] at this
    rw [← this]
    ext t ht
    simp only [BitVec.getElem_extractLsb', BitVec.getElem_xor, Mem.readW]
    simp
  · rfl

/-- One block of keystream XORed in, 16 bytes at a time, from the source to the destination. -/
theorem dataInv_stepX {m₀ m : Mem} {S D : Addr} {n k : Nat} {ks : Nat → Byte} {v : BitVec 128}
    (hsd : SrcDst S D n) (hn : 16 * n < 2 ^ 64) (hk : k < n) (h : DataInv m₀ m S D n k ks)
    (hsrc : SrcInv m₀ m S n k) (hks : ∀ t < 16, v.extractLsb' (8 * t) 8 = ks (16 * k + t)) :
    DataInv m₀ (xorXTo m (S + BitVec.ofNat 64 (16 * k)) (D + BitVec.ofNat 64 (16 * k)) v) S D n (k + 1) ks ∧
      SrcInv m₀ (xorXTo m (S + BitVec.ofNat 64 (16 * k)) (D + BitVec.ofNat 64 (16 * k)) v) S n (k + 1) ∧
      Frame [⟨D, 16 * n⟩] m (xorXTo m (S + BitVec.ofNat 64 (16 * k)) (D + BitVec.ofNat 64 (16 * k)) v) := by
  refine ⟨fun i hi => ?_, fun i hi hki => ?_, fun x hx => ?_⟩
  · rw [xorXTo_apply, off_toNat D (by omega_arith) (by omega_arith)]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · have ea : S + BitVec.ofNat 64 (16 * k) +
            (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 (16 * k))) = S + BitVec.ofNat 64 i := by
          rw [show D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 (16 * k)) = BitVec.ofNat 64 (i - 16 * k) by
              apply BitVec.eq_of_toNat_eq
              rw [off_toNat D (by omega_arith) (by omega_arith), ite_eq_left h1]
              simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega_arith)],
            add_ofNat_add, show 16 * k + (i - 16 * k) = i by omega_arith]
        rw [ite_eq_left h2, ea, hsrc i hi h1, hks _ h2, ite_eq_left (show i < 16 * (k + 1) by omega_arith),
          show 16 * k + (i - 16 * k) = i by omega_arith]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 16 * k by omega_arith),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega_arith)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega_arith), h i hi,
        ite_eq_left (show i < 16 * k by omega_arith), ite_eq_left (show i < 16 * (k + 1) by omega_arith)]
  · have hf := hsd.far (w := 16) hn hk (by omega_arith) hi fun _ => .inr (by omega_arith)
    rw [xorXTo_apply, ite_eq_right (by omega_arith), hsrc i hi (by omega_arith)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx ⟨D, 16 * n⟩ (List.mem_singleton_self _)
    rw [xorXTo_apply, ite_eq_right]
    have : 16 * k < 2 ^ 64 := by omega_arith
    have : (BitVec.ofNat 64 (16 * k)).toNat = 16 * k := by simp; omega_arith
    bv_omega

/-- Keystream block `k` of the group: quadword `k / 4` of `q (k % 4)`, then of `q (k % 4 + 4)`. -/
abbrev ksv (s : State) (k : Nat) : BitVec 128 := QX s (k / 4) (k % 4 + 4) ++ QX s (k / 4) (k % 4)

theorem extract_append (hi lo : BitVec 64) {t : Nat} (ht : t < 16) :
    (hi ++ lo).extractLsb' (8 * t) 8 =
      if t < 8 then lo.extractLsb' (8 * t) 8 else hi.extractLsb' (8 * (t - 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hj, Bool.true_and]
  split
  · rename_i h
    rw [ite_eq_left (show t < 8 by omega), BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
  · rename_i h
    rw [ite_eq_right (show ¬ t < 8 by omega), BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
    exact congrArg _ (by omega)

open VG.Impl.Aes.X86_64 (dstR) in
theorem xorBlock_ok (to : Bool) {s : State} {a d : Addr} {k : Nat} (hk : k < 8) (ha : s.gpr .rdx = a)
    (hd : s.gpr (dstR to) = d) (i1 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (16 * k)) 16)
    (h1 : InRegions s.wr (d + BitVec.ofNat 64 (16 * k)) 16) :
    ∃ s', runBlock isa (xorBlockG to k) s = some s' ∧
      s'.mem = xorXTo s.mem (a + BitVec.ofNat 64 (16 * k)) (d + BitVec.ofNat 64 (16 * k)) (ksv s k) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧ s'.cf = s.cf ∧
      (∀ i < 8, ∀ l, QX s' l i = QX s l i) := by
  have hne : ∀ i < 8, q i ≠ ta ∧ q i ≠ tb := by decide
  have hst : ∀ (u : BitVec 128), ∃ s', runBlock isa
      ([Instr.movdquLoad tb (at_ .rdx (16 * k)), pxor tb ta, Instr.movdquStore (at_ (dstR to) (16 * k)) tb] :
        List Instr)
      (s.setXmm ta u) = some s' ∧
      s'.mem = xorXTo s.mem (a + BitVec.ofNat 64 (16 * k)) (d + BitVec.ofNat 64 (16 * k)) u ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧ s'.cf = s.cf ∧ (∀ i < 8, ∀ l, QX s' l i = QX s l i) := by
    intro u
    refine ⟨_, by
      simp only [pxor, bin, runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec, State.load128,
        State.store128, State.ea, at_, ofInt_nat, VG.X86_64.RegUpd.gpr_setXmm, VG.X86_64.RegUpd.rd_setXmm,
        VG.X86_64.RegUpd.wr_setXmm, VG.X86_64.RegUpd.mem_setXmm, ha, hd, i1, h1, ite_true, Option.map_some]
      rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [xorXTo, xmm_setXmm_self, XBinOp.eval, xmm_setXmm_of_ne _ _ (show ta ≠ tb by decide)]
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · intro i hi l
      simp only [QX]
      rw [xmm_setXmm_of_ne _ _ (hne i hi).2, xmm_setXmm_of_ne _ _ (hne i hi).2, xmm_setXmm_of_ne _ _ (hne i hi).1]
  have e : xorBlockG to k = ksBlock k ++
      ([Instr.movdquLoad tb (at_ .rdx (16 * k)), pxor tb ta, Instr.movdquStore (at_ (dstR to) (16 * k)) tb] :
        List Instr) := rfl
  rw [e, VG.X86_64.runBlock_append]
  by_cases h4 : k < 4
  · obtain ⟨s', h', rest⟩ := hst (qword (s.xmm (q (k + 4))) 0 ++ qword (s.xmm (q k)) 0)
    refine ⟨s', ?_, ?_⟩
    · simp only [ksBlock, h4, ite_true, mova, bin, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
        XOp.exec, XBinOp.eval, xmm_setXmm_self, xmm_setXmm_of_ne _ _ (hne (k + 4) (by omega)).1, Option.bind_some]
      rw [VG.X86_64.setXmm_setXmm]
      exact h'
    · have e : ksv s k = qword (s.xmm (q (k + 4))) 0 ++ qword (s.xmm (q k)) 0 := by
        have hk4 : k / 4 = 0 := by omega
        have hkm : k % 4 = k := Nat.mod_eq_of_lt h4
        simp only [ksv, QX]; rw [hk4, hkm]
      rw [e]; exact rest
  · obtain ⟨s', h', rest⟩ := hst (qword (s.xmm (q k)) 1 ++ qword (s.xmm (q (k - 4))) 1)
    refine ⟨s', ?_, ?_⟩
    · simp only [ksBlock, h4, ite_false, mova, bin, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
        XOp.exec, XBinOp.eval, xmm_setXmm_self, xmm_setXmm_of_ne _ _ (hne k hk).1, Option.bind_some]
      rw [VG.X86_64.setXmm_setXmm]
      exact h'
    · have e : ksv s k = qword (s.xmm (q k)) 1 ++ qword (s.xmm (q (k - 4))) 1 := by
        have hk4 : k / 4 = 1 := by omega
        have hkm : k % 4 + 4 = k := by omega
        have hkm' : k % 4 = k - 4 := by omega
        simp only [ksv, QX]; rw [hk4, hkm, hkm']
      rw [e]; exact rest


/-! ## The XOR phase of a group -/

open VG.Proof.Aes.X86_64 (dataInv_mono clear_ok Mode Mode.sd dAddr dRegion dstLoad_wp dstAdv_wp dstSave_wp)
open VG.Impl.Aes.X86_64 (dstR)

/-- After `k` blocks of the group from `s₄`. -/
structure XS8 (m₀ : Mem) (S D : Addr) (n g : Nat) (ks : Nat → Byte) (s₄ : State) (k : Nat) (s : State) :
    Prop where
  data : DataInv m₀ s.mem S D n (4 * g + k) ks
  src : SrcInv m₀ s.mem S n (4 * g + k)
  frame : Frame [⟨D, 16 * n⟩] s₄.mem s.mem
  gpr : s.gpr = s₄.gpr
  lanes : ∀ i < 8, ∀ l, QX s l i = QX s₄ l i
  rd : s.rd = s₄.rd
  wr : s.wr = s₄.wr

/-- What the blocks of the XOR phase start from. -/
structure XReady8 (to : Bool) (m₀ : Mem) (S D : Addr) (n g : Nat) (ks : Nat → Byte) (s₄ : State) : Prop where
  hn : 16 * n < 2 ^ 64
  sd : SrcDst S D n
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₄.wr
  src : (⟨S, 16 * n⟩ : Region) ∈ s₄.rd ++ s₄.wr
  rdx : s₄.gpr .rdx = S + BitVec.ofNat 64 (64 * g)
  dst : s₄.gpr (dstR to) = D + BitVec.ofNat 64 (64 * g)
  r8 : s₄.gpr .r8 = BitVec.ofNat 64 (n - 4 * g)
  ks : ∀ k < 8, ∀ t < 16, (ksv s₄ k).extractLsb' (8 * t) 8 = ks (16 * (4 * g + k) + t)

/-- Before the XOR phase of the group from group `g` of four, five or more blocks left. -/
structure XPre8 (to : Bool) (m₀ : Mem) (S D b : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ : State) : Prop where
  hg : 4 * g + 4 < n
  hn : 16 * n < 2 ^ 64
  mode : Mode to S D n
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₃.wr
  src : (⟨S, 16 * n⟩ : Region) ∈ s₃.rd ++ s₃.wr
  scr : (⟨b, 2048⟩ : Region) ∈ s₃.wr
  base : s₃.gpr sb = b
  rdx : s₃.gpr .rdx = S + BitVec.ofNat 64 (64 * g)
  slot : to = true → s₃.mem.readW (dAddr b) 64 = D + BitVec.ofNat 64 (64 * g)
  r8 : s₃.gpr .r8 = BitVec.ofNat 64 (n - 4 * g)
  sslot : Region.Disjoint ⟨S, 16 * n⟩ (dRegion b)
  dslot : Region.Disjoint ⟨D, 16 * n⟩ (dRegion b)
  data : DataInv m₀ s₃.mem S D n (4 * g) ks
  srcInv : SrcInv m₀ s₃.mem S n (4 * g)
  ks : ∀ k < 8, ∀ t < 16, (ksv s₃ k).extractLsb' (8 * t) 8 = ks (16 * (4 * g + k) + t)

/-- After the XOR phase: ZF is set if no data is left. -/
def XDone8 (to : Bool) (m₀ : Mem) (S D b : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ s : State) : Prop :=
  Frame [⟨D, 16 * n⟩, dRegion b] s₃.mem s.mem ∧
    (∀ r, r ≠ VG.Impl.Aes.X86_64.t1 → r ≠ .rdx → r ≠ .r8 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧
    ((s.zf = some true ∧ DataInv m₀ s.mem S D n n ks) ∨
     (s.zf = some false ∧ 4 * g + 8 < n ∧ DataInv m₀ s.mem S D n (4 * (g + 2)) ks ∧
      SrcInv m₀ s.mem S n (4 * (g + 2)) ∧
      s.gpr .rdx = S + BitVec.ofNat 64 (64 * (g + 2)) ∧ s.gpr .r8 = BitVec.ofNat 64 (n - 4 * (g + 2)) ∧
      (to = true → s.mem.readW (dAddr b) 64 = D + BitVec.ofNat 64 (64 * (g + 2)))))

section Xor

variable {to : Bool} {m₀ : Mem} {S D : Addr} {n g : Nat} {ks : Nat → Byte} {s₄ : State}

theorem ksv_congr {s s' : State} (h : ∀ i < 8, ∀ l, QX s' l i = QX s l i) {k : Nat} :
    ksv s' k = ksv s k := by
  simp only [ksv]; rw [h _ (by omega), h _ (by omega)]

theorem xs8_step (hp : XReady8 to m₀ S D n g ks s₄) {k : Nat} (hk : k < 8) (hkn : 4 * g + k < n) {s : State}
    (hs : XS8 m₀ S D n g ks s₄ k s) {P : State → Prop} (h : ∀ s', XS8 m₀ S D n g ks s₄ (k + 1) s' → P s') :
    WP isa (.block (xorBlockG to k)) s P := by
  have hn := hp.hn
  have hA : ∀ X : Addr, X + BitVec.ofNat 64 (64 * g) + BitVec.ofNat 64 (16 * k) =
      X + BitVec.ofNat 64 (16 * (4 * g + k)) := fun X => by
    rw [add_ofNat_add]; congr 2; omega_arith
  have hsrc : (⟨S, 16 * n⟩ : Region) ∈ s.rd ++ s.wr := by rw [hs.rd, hs.wr]; exact hp.src
  have i1 := in_off hsrc (off := 16 * (4 * g + k)) (n := 16) (by omega_arith) hn
  have j1 := in_off (hs.wr ▸ hp.dat) (off := 16 * (4 * g + k)) (n := 16) (by omega_arith) hn
  rw [← hA] at i1 j1
  obtain ⟨s', hs', hm, hg', hrd, hwr, -, -, hl⟩ :=
    xorBlock_ok to hk (by rw [hs.gpr]; exact hp.rdx) (by rw [hs.gpr]; exact hp.dst) i1 j1
  rw [hA S, hA D] at hm
  have hst := dataInv_stepX (v := ksv s k) hp.sd hn hkn hs.data hs.src (fun t ht => by
    rw [ksv_congr hs.lanes]; exact hp.ks k hk t ht)
  rw [← hm] at hst
  exact WP.of_runBlock ⟨s', hs', h s' ⟨hst.1, hst.2.1, hs.frame.trans hst.2.2, hg'.trans hs.gpr,
    fun i hi l => (hl i hi l).trans (hs.lanes i hi l), hrd.trans hs.rd, hwr.trans hs.wr⟩⟩

theorem cmp8_wp {s : State} {r : Reg} {k : BitVec 32} {K v : Nat} (hr : s.gpr r = BitVec.ofNat 64 v)
    (hv : v < 2 ^ 64) (hk : (k.signExtend 64).toNat = K) {P : State → Prop}
    (h : ∀ s', s'.cf = some (decide (v < K)) → s'.gpr = s.gpr → s'.mem = s.mem → s'.xmm = s.xmm →
      s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block [.alu .cmp r (.imm k)]) s P := by
  refine WP.of_runBlock ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, execAlu,
    readSrc, Option.bind_some]; rfl, ?_⟩
  exact h _ (by simp [arithFlags, State.setFlags, hr, hk]; rw [Nat.mod_eq_of_lt (by simpa using hv)])
    rfl rfl rfl rfl rfl

theorem advance8_ok (s : State) :
    ∃ s', runBlock isa [.alu .add .rdx (.imm 128), .alu .sub .r8 (.imm 8)] s = some s' ∧
      s'.gpr .rdx = s.gpr .rdx + 128 ∧ s'.gpr .r8 = s.gpr .r8 - 8 ∧ s'.zf = some (s.gpr .r8 - 8 == 0) ∧
      (∀ r, r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_⟩
  simp only [State.setReg, arithFlags, State.setFlags, show (8 : BitVec 32).signExtend 64 = 8 by decide,
    show (128 : BitVec 32).signExtend 64 = 128 by decide]
  exact ⟨by simp, by simp, rfl, fun r h1 h2 => by simp [h1, h2], trivial, trivial, trivial⟩

open VG.Impl.Aes.X86_64 (dstAdv dstSave) in
theorem xorFull_eq : xorFullG to = xorBlockG to 0 ++ xorBlockG to 1 ++ xorBlockG to 2 ++ xorBlockG to 3 ++
    xorBlockG to 4 ++ xorBlockG to 5 ++ xorBlockG to 6 ++ xorBlockG to 7 ++
    (dstAdv to 128 ++ dstSave to) ++ ([.alu .add .rdx (.imm 128), .alu .sub .r8 (.imm 8)] : List Instr) := by
  simp only [xorFullG, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]

theorem xorTail5_eq : (List.range 5).flatMap (xorBlockG to) = xorBlockG to 0 ++ xorBlockG to 1 ++
    xorBlockG to 2 ++ xorBlockG to 3 ++ xorBlockG to 4 := by
  simp only [List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]

theorem ofNat_sub_eight {x : Nat} (h : 8 ≤ x) : BitVec.ofNat 64 x - 8 = BitVec.ofNat 64 (x - 8) :=
  Offset.ofNat_sub_ofNat h

theorem ofNat_sub_eight_ne {x : Nat} (hx : x < 2 ^ 64) (h : 8 ≤ x) (hne : x ≠ 8) :
    BitVec.ofNat 64 x - 8 ≠ 0 := by
  bv_omega

theorem off_add128 (D : Addr) (g : Nat) :
    D + BitVec.ofNat 64 (64 * g) + 128 = D + BitVec.ofNat 64 (64 * (g + 2)) :=
  (Offset.add_add D _ 128).trans (by rw [show 64 * g + 128 = 64 * (g + 2) by omega_arith])

/-- The data invariants through a frame that misses the source and the destination. -/
theorem XS8.frame_slot {k : Nat} {s s' : State} (hs : XS8 m₀ S D n g ks s₄ k s) (hn : 16 * n < 2 ^ 64)
    {b : Addr} (hf : Frame [dRegion b] s.mem s'.mem) (hS : Region.Disjoint ⟨S, 16 * n⟩ (dRegion b))
    (hD : Region.Disjoint ⟨D, 16 * n⟩ (dRegion b)) :
    DataInv m₀ s'.mem S D n (4 * g + k) ks ∧ SrcInv m₀ s'.mem S n (4 * g + k) :=
  ⟨fun i hi => by rw [← hs.data i hi]; exact hf.bytes (R := ⟨D, 16 * n⟩) (by simpa using hD) (by simp only; omega_arith) hi,
   fun i hi hk => by rw [← hs.src i hi hk]; exact hf.bytes (R := ⟨S, 16 * n⟩) (by simpa using hS) (by simp only; omega_arith) hi⟩

open VG.Impl.Aes.X86_64 (dstLoad) in
theorem xorPhase8_wp {b : Addr} {s₃ : State} (hp : XPre8 to m₀ S D b n g ks s₃) :
    WP isa (.seq (.block (dstLoad to ++ [.alu .cmp .r8 (.imm 8)])) (.ite .ae (.block (xorFullG to)) (xorTailG to)))
      s₃ (XDone8 to m₀ S D b n g ks s₃) := by
  have hg := hp.hg
  have hn := hp.hn
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa)]
  refine dstLoad_wp to hp.base hp.scr fun s₄' dl₄ o₄' m₄' x₄' rd₄' wr₄' => ?_
  refine cmp8_wp ((o₄' .r8 (by decide)).trans hp.r8) (by omega_arith) (K := 8) (by decide)
    fun s₄ cf₄ g₄ m₄ x₄ rd₄ wr₄ => ?_
  have k₄ : ∀ r, r ≠ VG.Impl.Aes.X86_64.t1 → s₄.gpr r = s₃.gpr r := fun r hr => by rw [g₄]; exact o₄' r hr
  have mm₄ : s₄.mem = s₃.mem := m₄.trans m₄'
  have xx₄ : s₄.xmm = s₃.xmm := x₄.trans x₄'
  have hr : XReady8 to m₀ S D n g ks s₄ :=
    { hn, sd := hp.mode.sd
      dat := by rw [wr₄, wr₄']; exact hp.dat
      src := by rw [rd₄, wr₄, rd₄', wr₄']; exact hp.src
      rdx := (k₄ .rdx (by decide)).trans hp.rdx
      dst := by
        rcases hp.mode with ⟨rfl, rfl⟩ | ⟨rfl, _⟩
        · exact (k₄ .rdx (by decide)).trans hp.rdx
        · show s₄.gpr VG.Impl.Aes.X86_64.t1 = _
          rw [g₄, dl₄ rfl]; exact hp.slot rfl
      r8 := (k₄ .r8 (by decide)).trans hp.r8
      ks := fun k hk t ht => by
        rw [ksv_congr (s' := s₄) (s := s₃) (fun i _ l => by simp only [QX, xx₄])]; exact hp.ks k hk t ht }
  have x₀ : XS8 m₀ S D n g ks s₄ 0 s₄ :=
    ⟨by rw [mm₄, Nat.add_zero]; exact hp.data, by rw [mm₄, Nat.add_zero]; exact hp.srcInv,
      Frame.refl _ _, rfl, fun _ _ _ => rfl, rfl, rfl⟩
  have hb₄ : s₄.gpr sb = b := (k₄ sb (by decide)).trans hp.base
  have hscr₄ : (⟨b, 2048⟩ : Region) ∈ s₄.wr := by rw [wr₄, wr₄']; exact hp.scr
  have fin : ∀ {k : Nat} {s s' : State}, XS8 m₀ S D n g ks s₄ k s → Frame [dRegion b] s.mem s'.mem →
      Frame [⟨D, 16 * n⟩, dRegion b] s₃.mem s'.mem := fun x f => by
    rw [← mm₄]
    exact (x.frame.mono fun r hr => by simp at hr; simp [hr]).trans (f.mono fun r hr => by simp at hr; simp [hr])
  refine WP.ite (!decide (n - 4 * g < 8)) (by simp [X86_64.eval, cf₄]) (fun hb => ?_) (fun hb => ?_)
  · -- Eight blocks.
    have h8 : 8 ≤ n - 4 * g := by simpa using hb
    rw [xorFull_eq]
    repeat rw [WP.block_append_iff (M := isa)]
    refine xs8_step hr (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₅ x₅ => ?_
    refine xs8_step hr (k := 1) (by omega_arith) (by omega_arith) x₅ fun s₆ x₆ => ?_
    refine xs8_step hr (k := 2) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
    refine xs8_step hr (k := 3) (by omega_arith) (by omega_arith) x₇ fun s₈ x₈ => ?_
    refine xs8_step hr (k := 4) (by omega_arith) (by omega_arith) x₈ fun s₉ x₉ => ?_
    refine xs8_step hr (k := 5) (by omega_arith) (by omega_arith) x₉ fun s₁₀ x₁₀ => ?_
    refine xs8_step hr (k := 6) (by omega_arith) (by omega_arith) x₁₀ fun s₁₁ x₁₁ => ?_
    refine xs8_step hr (k := 7) (by omega_arith) (by omega_arith) x₁₁ fun s₁₂ x₁₂ => ?_
    have hb₁₂ : s₁₂.gpr sb = b := by rw [x₁₂.gpr]; exact hb₄
    rw [WP.block_append_iff (M := isa)]
    refine dstAdv_wp to 128 (by decide) fun s₁₃ a₁₃ o₁₃ m₁₃ rd₁₃ wr₁₃ => ?_
    refine dstSave_wp to (s := s₁₃) ((o₁₃ sb (by decide)).trans hb₁₂) (by rw [wr₁₃, x₁₂.wr]; exact hscr₄)
      fun s₁₄ sl₁₄ g₁₄ f₁₄ rd₁₄ wr₁₄ => ?_
    obtain ⟨s₁₅, hs₁₅, d₁₅, r₁₅, z₁₅, o₁₅, m₁₅, rd₁₅, wr₁₅⟩ := advance8_ok s₁₄
    refine WP.of_runBlock ⟨s₁₅, hs₁₅, ?_⟩
    have f₁₃ : Frame [dRegion b] s₁₂.mem s₁₄.mem := m₁₃ ▸ f₁₄
    obtain ⟨dat₁₄, src₁₄⟩ := x₁₂.frame_slot hn f₁₃ hp.sslot hp.dslot
    have kk : ∀ r, r ≠ VG.Impl.Aes.X86_64.t1 → s₁₄.gpr r = s₃.gpr r := fun r h1 => by
      rw [g₁₄, o₁₃ r h1, x₁₂.gpr, k₄ r h1]
    have e₁ : s₁₄.gpr .rdx = S + BitVec.ofNat 64 (64 * g) := (kk .rdx (by decide)).trans hp.rdx
    have e₂ : s₁₄.gpr .r8 = BitVec.ofNat 64 (n - 4 * g) := (kk .r8 (by decide)).trans hp.r8
    refine ⟨m₁₅ ▸ fin x₁₂ f₁₃, fun r h1 h2 h3 => (o₁₅ r h2 h3).trans (kk r h1),
      by rw [rd₁₅, rd₁₄, rd₁₃, x₁₂.rd, rd₄, rd₄'], by rw [wr₁₅, wr₁₄, wr₁₃, x₁₂.wr, wr₄, wr₄'], ?_⟩
    rw [z₁₅, e₂, m₁₅]
    by_cases hl : n - 4 * g = 8
    · refine .inl ⟨?_, dataInv_mono dat₁₄ (by omega_arith) (by omega_arith)⟩
      rw [hl]; rfl
    · refine .inr ⟨?_, by omega_arith, by simpa [Nat.mul_add] using dat₁₄, by simpa [Nat.mul_add] using src₁₄,
        ?_, ?_, fun ht => ?_⟩
      · simp only [Option.some.injEq, beq_eq_false_iff_ne]
        exact ofNat_sub_eight_ne (by omega_arith) h8 hl
      · rw [d₁₅, e₁]; exact off_add128 S g
      · rw [r₁₅, e₂, ofNat_sub_eight h8, show n - 4 * (g + 2) = n - 4 * g - 8 by omega_arith]
      · subst ht
        rw [sl₁₄ rfl, a₁₃ rfl, x₁₂.gpr]
        have := hr.dst
        exact (congrArg (· + BitVec.ofNat 64 128) this).trans (off_add128 D g)
  · -- The last five to seven blocks.
    have h8 : n - 4 * g < 8 := by simpa using hb
    unfold xorTailG
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa), xorTail5_eq]
    repeat rw [WP.block_append_iff (M := isa)]
    refine xs8_step hr (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₅ x₅ => ?_
    refine xs8_step hr (k := 1) (by omega_arith) (by omega_arith) x₅ fun s₆ x₆ => ?_
    refine xs8_step hr (k := 2) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
    refine xs8_step hr (k := 3) (by omega_arith) (by omega_arith) x₇ fun s₈ x₈ => ?_
    refine xs8_step hr (k := 4) (by omega_arith) (by omega_arith) x₈ fun s₉ x₉ => ?_
    refine cmp8_wp (by rw [x₉.gpr]; exact hr.r8) (by omega_arith) (K := 6) (by decide)
      fun s₁₀ cf₁₀ g₁₀ m₁₀ xm₁₀ rd₁₀ wr₁₀ => ?_
    have x₁₀ : XS8 m₀ S D n g ks s₄ 5 s₁₀ := ⟨m₁₀ ▸ x₉.data, m₁₀ ▸ x₉.src, m₁₀ ▸ x₉.frame, g₁₀.trans x₉.gpr,
      fun i hi l => by simp only [QX, xm₁₀]; exact x₉.lanes i hi l, rd₁₀.trans x₉.rd, wr₁₀.trans x₉.wr⟩
    refine WP.seq (WP.mono (Q := XS8 m₀ S D n g ks s₄ (n - 4 * g)) ?_ fun s hs => ?_)
    · refine WP.ite (!decide (n - 4 * g < 6)) (by simp [X86_64.eval, cf₁₀]) (fun hb => ?_) (fun hb => ?_)
      · have h6 : 6 ≤ n - 4 * g := by simpa using hb
        refine WP.seq ?_
        rw [WP.block_append_iff (M := isa)]
        refine xs8_step hr (k := 5) (by omega_arith) (by omega_arith) x₁₀ fun s₁₁ x₁₁ => ?_
        refine cmp8_wp (by rw [x₁₁.gpr]; exact hr.r8) (by omega_arith) (K := 7) (by decide)
          fun s₁₂ cf₁₂ g₁₂ m₁₂ xm₁₂ rd₁₂ wr₁₂ => ?_
        have x₁₂ : XS8 m₀ S D n g ks s₄ 6 s₁₂ := ⟨m₁₂ ▸ x₁₁.data, m₁₂ ▸ x₁₁.src, m₁₂ ▸ x₁₁.frame,
          g₁₂.trans x₁₁.gpr, fun i hi l => by simp only [QX, xm₁₂]; exact x₁₁.lanes i hi l,
          rd₁₂.trans x₁₁.rd, wr₁₂.trans x₁₁.wr⟩
        refine WP.ite (!decide (n - 4 * g < 7)) (by simp [X86_64.eval, cf₁₂]) (fun hb => ?_) (fun hb => ?_)
        · have h7 : n - 4 * g = 6 + 1 := by simp at hb; omega_arith
          refine xs8_step hr (k := 6) (by omega_arith) (by omega_arith) x₁₂ fun s₁₃ x₁₃ => ?_
          rw [h7]; exact x₁₃
        · have h7 : n - 4 * g = 6 := by simp at hb; omega_arith
          exact WP.block_nil (by rw [h7]; exact x₁₂)
      · have h5 : n - 4 * g = 5 := by simp at hb; omega_arith
        exact WP.block_nil (by rw [h5]; exact x₁₀)
    · rw [WP.block_append_iff (M := isa)]
      refine dstSave_wp to (s := s) (by rw [hs.gpr]; exact hb₄) (hs.wr ▸ hscr₄)
        fun s₁₄ _ g₁₄ f₁₄ rd₁₄ wr₁₄ => ?_
      obtain ⟨s', hs', z', o', m', rd', wr'⟩ := clear_ok s₁₄
      obtain ⟨dat₁₄, -⟩ := hs.frame_slot hn f₁₄ hp.sslot hp.dslot
      refine WP.of_runBlock ⟨s', hs', m' ▸ fin hs f₁₄, fun r h1 _ h3 => by
          rw [o' r h3, g₁₄, hs.gpr, k₄ r h1],
        by rw [rd', rd₁₄, hs.rd, rd₄, rd₄'], by rw [wr', wr₁₄, hs.wr, wr₄, wr₄'], .inl ⟨z', ?_⟩⟩
      rw [show 4 * g + (n - 4 * g) = n by omega_arith] at dat₁₄
      rw [m']; exact dat₁₄

end Xor


/-! ## A group -/

open VG.Proof.Aes.X86_64 (GSetup GInv GDone gRegions ctr_inRel dataInv_frame srcInv_frame keysAt_frame scr_disj
  scr_sub KSetup slot_read_frame)

theorem hiWord_add (hi : BitVec 64) (C : BitVec 32) (k i : Nat) :
    hiWord hi (C + BitVec.ofNat 32 k) i = hiWord hi C (i + k) := by
  simp only [hiWord, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm k i]

/-- The counter blocks of the group in each quadword, as `InRel` has them. -/
theorem ctr_lanes {s : State} {icb : Spec.Gcm.Block} {lo hi : BitVec 64} {C : BitVec 32} {g : Nat}
    (hlo : ∀ i < 8, ∀ j < 8, lo.getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - i) + j))
    (hhi : ∀ i < 4, ∀ j < 8, hi.getLsbD (8 * i + j) = icb.getLsbD (8 * (7 - i) + j))
    (hhi' : ∀ p, 32 ≤ p → hi.getLsbD p = false)
    (hC : C = icb.extractLsb' 0 32 + BitVec.ofNat 32 (4 * g))
    (hQ : ∀ c < 4, ∀ l < 2, QX s l c = lo ∧ QX s l (c + 4) = hiWord hi C (c + 4 * l)) :
    ∀ l < 2, InRel (QX s l) (fun c => VG.Proof.Aes.ctrState icb (4 * (g + l) + c)) := by
  intro l hl
  refine ctr_inRel hlo hhi hhi' (C := C + BitVec.ofNat 32 (4 * l)) ?_ fun c hc => ?_
  · rw [hC, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]
  · rw [hiWord_add]; exact hQ c hc l hl


/-- The keystream blocks of the group, from the encrypted counter blocks in each quadword. -/
theorem ks_lanes {s : State} {R g : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (h : ∀ l < 2, InRel (QX s l) (fun c => Spec.Aes.cipher R w (ctrState icb (4 * (g + l) + c)))) :
    ∀ k < 8, ∀ t < 16, (ksv s k).extractLsb' (8 * t) 8 = keyStream R w icb (16 * (4 * g + k) + t) := by
  intro k hk t ht
  have hc := ks_of_inRel (h (k / 4) (by omega)) (c := k % 4) (by omega) ht
  rw [show 4 * (g + k / 4) + k % 4 = 4 * g + k by omega] at hc
  rw [ksv, extract_append _ _ ht, ← hc]
  by_cases h8 : t < 8
  · rw [ite_eq_left h8, show t / 8 = 0 by omega, show t % 8 = t by omega, Nat.mul_zero, Nat.add_zero]
  · rw [ite_eq_right h8, show t / 8 = 1 by omega, show t % 8 = t - 8 by omega, Nat.mul_one]

theorem groupSetup_ok (s : State) :
    ∃ s', runBlock isa groupSetup s = some s' ∧ s'.gpr .rcx = s.gpr .r9 ∧
      s'.gpr .r11 = s.gpr .r9 + BitVec.ofNat 64 srOff ∧
      (∀ r, r ≠ .rcx → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.xmm = s.xmm := by
  refine ⟨_, by simp only [groupSetup, runBlock_cons, runStep_some, runBlock_nil, reduceExec, execAlu,
    readSrc, Option.bind_some, Option.map_some]; rfl, ?_⟩
  simp only [State.setReg, arithFlags, State.setFlags,
    show (BitVec.ofNat 32 srOff).signExtend 64 = BitVec.ofNat 64 srOff by decide]
  exact ⟨by simp, by simp, fun r h1 h2 => by simp [h1, h2], trivial, trivial, trivial, trivial⟩

/-- ShiftRows' masks, 464 bytes into the scratch buffer at `b`. -/
def MasksAt (m : Mem) (b : Addr) : Prop :=
  ∀ k < 2, ∀ l < 2, qword (m.readW (b + BitVec.ofNat 64 (srOff + 16 * k)) 128) l = (srMasks.getD k (0, 0)).2

/-- One group of eight blocks (or the last five to seven): from before group `g` of four, with
more than four blocks left, to after the last group (ZF set) or before group `g + 2`. -/
theorem sseGroup_ok {to : Bool} {m₀ : Mem} {s₂ : State} {b S D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : GSetup to s₂ b S D n R w icb) (hmask : MasksAt s₂.mem b) {g : Nat}
    {s : State} (hi : GInv to m₀ s₂ b S D n R w icb g s) (h5 : 4 * g + 4 < n) :
    WP isa (sseGroupG to) s fun s' => (s'.zf = some true ∧ GDone m₀ s₂ b S D n R w icb s') ∨
      (s'.zf = some false ∧ GInv to m₀ s₂ b S D n R w icb (g + 2) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega_arith
  have hn := hs.hn
  have hscr : (⟨b, 2048⟩ : Region) ∈ s.wr := hi.wr ▸ hs.scr
  unfold sseGroupG
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₀, h₀, rcx₀, r11₀, o₀, m₀', rd₀, wr₀, x₀⟩ := groupSetup_ok s
  refine WP.of_runBlock ⟨s₀, h₀, ?_⟩
  have hb₀ : s₀.gpr sb = b := (o₀ sb (by decide) (by decide)).trans hi.base
  refine WP.mono (ctrBlocks_wp hb₀ (wr₀ ▸ hscr)) fun s₁ ⟨hq₁, o₁, m₁, rd₁, wr₁⟩ => ?_
  have hb₁ : s₁.gpr sb = b := (o₁ sb (by decide) (by decide)).trans hb₀
  have c448 : (⟨b + BitVec.ofNat 64 (8 * 56), 4⟩ : Region).Contains
      (b + BitVec.ofNat 64 (8 * 56)) (32 / 8) := Region.contains_self _ _
  have f₁ : Frame [⟨b + BitVec.ofNat 64 (8 * 56), 4⟩] s.mem s₁.mem := by
    rw [m₁, m₀']; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c448
  have hf₁ : Frame (gRegions b D n) s₂.mem s₁.mem :=
    hi.frame.trans (f₁.mono fun r hr => by simp at hr; simp [hr])
  have clo : cloW s₀.mem b = cloW s₂.mem b := by
    rw [m₀']
    exact hi.frame.readW (Region.contains_self _ _) (hs.slot_disj (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  have chi : chiW s₀.mem b = chiW s₂.mem b := by
    rw [m₀']
    exact hi.frame.readW (Region.contains_self _ _) (hs.slot_disj (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  have hp : EncPre s₁ R w :=
    ⟨by rw [hb₁, wr₁, wr₀, hi.wr]; exact hs.scr, hs.rounds,
      by rw [o₁ .rdi (by decide) (by decide), o₀ .rdi (by decide) (by decide), hi.rdi, hb₁],
      by rw [o₁ .rdi (by decide) (by decide), o₀ .rdi (by decide) (by decide), hi.rdi]
         exact keysAt_frame hR hf₁ hs.keys_disj hs.keys⟩
  have r9₁ : s₁.gpr .r9 = b := hb₁
  have r9 : s.gpr .r9 = b := hi.base
  have hq : SsePre s₁ :=
    { rcx := by rw [o₁ .rcx (by decide) (by decide), rcx₀, r9₁]; exact hi.base
      r11 := by rw [o₁ .r11 (by decide) (by decide), r11₀, r9₁, r9]
      masks := fun k hk l hl => by
        rw [o₁ .r11 (by decide) (by decide), r11₀, r9, Offset.add_add]
        rw [hf₁.readW (Region.contains_self _ _) (hs.slot_disj (by simp only [srOff]; omega_arith)
          (by simp only [srOff]; omega_arith) (by simp only [srOff]; omega_arith)) (by decide)]
        exact hmask k hk l hl }
  have hin : ∀ l < 2, InRel (QX s₁ l) (fun c => ctrState icb (4 * (g + l) + c)) :=
    ctr_lanes (by rw [clo]; exact hs.lo) (by rw [chi]; exact hs.hi) (by rw [chi]; exact hs.hi')
      (by rw [m₀']; exact hi.num) hq₁
  refine WP.seq (WP.mono (encrypt8_ok hp hq hin) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [r9₁] at fr₃
  have fr₃' : Frame [⟨b + BitVec.ofNat 64 0, 384⟩] s₁.mem s₃.mem := by simpa using fr₃
  obtain ⟨dat₁, src₁⟩ := hs.inv_frame (by omega_arith) f₁ hi.data hi.src
  obtain ⟨dat₃, src₃⟩ := hs.inv_frame (by omega_arith) fr₃' dat₁ src₁
  have hx : XPre8 to m₀ S D b n g (keyStream R w icb) s₃ :=
    { hg := h5, hn := hn, mode := hs.mode
      dat := by rw [hc₃.wr, wr₁, wr₀, hi.wr]; exact hs.dat
      src := by rw [hc₃.rd, hc₃.wr, rd₁, wr₁, rd₀, wr₀, hi.rd, hi.wr]; exact hs.src
      scr := by rw [hc₃.wr, wr₁, wr₀]; exact hscr
      base := by rw [hc₃.keep sb (by decide) (by decide), hb₁]
      rdx := by rw [hc₃.keep .rdx (by decide) (by decide), o₁ .rdx (by decide) (by decide),
        o₀ .rdx (by decide) (by decide), hi.rdx]
      slot := fun ht => by
        rw [slot_read_frame fr₃' (by omega_arith) (by omega_arith),
          slot_read_frame f₁ (by omega_arith) (by omega_arith), hi.slot ht]
      r8 := by rw [hc₃.keep .r8 (by decide) (by decide), o₁ .r8 (by decide) (by decide),
        o₀ .r8 (by decide) (by decide), hi.r8]
      sslot := hs.src_disj (by (try simp only [VG.Impl.Aes.X86_64.dSlot]); omega_arith)
      dslot := hs.dat_disj (by (try simp only [VG.Impl.Aes.X86_64.dSlot]); omega_arith)
      data := dat₃, srcInv := src₃
      ks := ks_lanes hin₃ }
  refine WP.mono (xorPhase8_wp hx) fun s' ⟨f', o', rd', wr', hz⟩ => ?_
  have keep : ∀ r, r ≠ .rax → r ≠ kp → r ≠ .rcx → r ≠ .r11 → r ≠ .r10 → r ≠ .rdx → r ≠ .r8 →
      r ≠ VG.Impl.Aes.X86_64.t1 → s'.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 h7 h8 => by
      rw [o' r h8 h6 h7, hc₃.keep r h1 h2, o₁ r h1 h5, o₀ r h3 h4]
  have base' : s'.gpr sb = b := by
    rw [keep sb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hi.base
  have rsp' : s'.gpr .rsp = s₂.gpr .rsp := by
    rw [keep .rsp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hi.rsp
  have rd'' : s'.rd = s₂.rd := by rw [rd', hc₃.rd, rd₁, rd₀, hi.rd]
  have wr'' : s'.wr = s₂.wr := by rw [wr', hc₃.wr, wr₁, wr₀, hi.wr]
  have frame' : Frame (gRegions b D n) s₂.mem s'.mem :=
    hf₁.trans ((fr₃.mono fun r hr => by simp at hr; simp [hr]).trans (f'.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
  rcases hz with ⟨z, d⟩ | ⟨z, h8, d, sr, rdx', r8', sl'⟩
  · exact .inl ⟨z, base', rsp', rd'', wr'', frame', d⟩
  · refine .inr ⟨z, ⟨by omega_arith, rdx', sl', r8', base', ?_, rsp', rd'', wr'', frame', ?_, d, sr⟩⟩
    · rw [keep .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hi.rdi]
    · have e₁ : numW s'.mem b = numW s₃.mem b :=
        f'.readW (Region.contains_self _ _) (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨(hs.dat_disj (by omega_arith)).symm,
            Offset.disjoint b (by (try simp only [VG.Impl.Aes.X86_64.dSlot]); omega_arith)
              (by (try simp only [VG.Impl.Aes.X86_64.dSlot]); omega_arith)
              (by (try simp only [VG.Impl.Aes.X86_64.dSlot]); omega_arith)⟩) (by decide)
      have e₂ : numW s₃.mem b = numW s₁.mem b :=
        fr₃.readW (Region.contains_self _ _) (by simpa using (scr_disj b (by omega_arith) (by omega_arith)).symm)
          (by decide)
      rw [e₁, e₂, m₁, numW, Mem.readW_writeW_self32, m₀', hi.num, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp
      omega_arith


/-! ## The masks, and the loop over the groups -/

theorem maskStore_ok {s : State} {b : Addr} (k : Nat) (v : BitVec 64) (hb : s.gpr .r9 = b)
    (hin : InRegions s.wr (b + BitVec.ofNat 64 (srOff + 16 * k)) 16) :
    ∃ s', runBlock isa (mkMask t0 v ++ ([.movdquStore (at_ .r9 (srOff + 16 * k)) t0] : List Instr)) s = some s' ∧
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (srOff + 16 * k))
        (qword ((0 : BitVec 64) ++ v) 0 ++ qword ((0 : BitVec 64) ++ v) 0) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hea : (((s.setReg .rax v).setXmm t0 ((0 : BitVec 64) ++ (s.setReg .rax v).gpr .rax)).setXmm t0
      (XBinOp.punpcklqdq.eval ((0 : BitVec 64) ++ (s.setReg .rax v).gpr .rax)
        ((0 : BitVec 64) ++ (s.setReg .rax v).gpr .rax))).ea (at_ .r9 (srOff + 16 * k)) =
      b + BitVec.ofNat 64 (srOff + 16 * k) := by
    simp only [State.ea, at_, VG.X86_64.RegUpd.gpr_setXmm, VG.X86_64.RegUpd.gpr_setReg_of_ne _ _
      (show ¬ Reg.r9 = .rax by decide), hb]
    congr 1
  refine ⟨_, by
    simp only [mkMask, bin, List.cons_append, List.nil_append, runBlock_cons, runStep_some, reduceExec,
      XOp.exec, xmm_setXmm_self]
    rw [State.store128, hea]
    simp only [VG.X86_64.RegUpd.wr_setXmm, VG.X86_64.RegUpd.wr_setReg, hin, ite_true, runStep_some,
      runBlock_nil]
    rfl, ?_, ?_, ?_, ?_⟩
  · simp only [VG.X86_64.RegUpd.mem_setXmm, VG.X86_64.RegUpd.mem_setReg, XBinOp.eval,
      VG.X86_64.RegUpd.gpr_setReg_self]
  · intro r hr
    simp only [VG.X86_64.RegUpd.gpr_setXmm]
    exact VG.X86_64.RegUpd.gpr_setReg_of_ne _ _ hr
  · rfl
  · rfl

theorem srSetup_eq : srSetup =
    (mkMask t0 0xFFFF0000FFFF0000 ++ ([.movdquStore (at_ .r9 (srOff + 16 * 0)) t0] : List Instr)) ++
    (mkMask t0 0xFFFFFFFF00000000 ++ ([.movdquStore (at_ .r9 (srOff + 16 * 1)) t0] : List Instr)) := rfl

theorem srSetup_ok {s : State} {b : Addr} (hb : s.gpr .r9 = b) (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) :
    ∃ s', runBlock isa srSetup s = some s' ∧ MasksAt s'.mem b ∧
      Frame [⟨b + BitVec.ofNat 64 srOff, 32⟩] s.mem s'.mem ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o0 := in_off hw (off := srOff + 16 * 0) (n := 16) (by simp [srOff]) (by omega_arith)
  have o1 := in_off hw (off := srOff + 16 * 1) (n := 16) (by simp [srOff]) (by omega_arith)
  obtain ⟨s₁, h₁, m₁, g₁, rd₁, wr₁⟩ := maskStore_ok 0 0xFFFF0000FFFF0000 hb o0
  obtain ⟨s₂, h₂, m₂, g₂, rd₂, wr₂⟩ := maskStore_ok (s := s₁) 1 0xFFFFFFFF00000000
    ((g₁ _ (by decide)).trans hb) (wr₁ ▸ o1)
  have hsep : Mem.Sep (b + BitVec.ofNat 64 (srOff + 16 * 0)) (128 / 8)
      (b + BitVec.ofNat 64 (srOff + 16 * 1)) (128 / 8) :=
    Offset.sep b (by simp [srOff]) (by simp [srOff]) (by simp [srOff])
  refine ⟨s₂, by rw [srSetup_eq, VG.X86_64.runBlock_append, h₁, Option.bind_some, h₂], fun k hk l hl => ?_,
    ?_, fun r hr => (g₂ r hr).trans (g₁ r hr), rd₂.trans rd₁, wr₂.trans wr₁⟩
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · rw [m₂, Mem.readW_writeW_sep hsep (by decide), m₁,
        Mem.readW_writeW_self _ _ 16 _ (by decide)]
      exact qword_dup _ hl
    · rw [m₂, Mem.readW_writeW_self _ _ 16 _ (by decide)]
      exact qword_dup _ hl
  · rw [m₂, m₁]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
    · exact Offset.contains b (by simp [srOff]) (by simp [srOff]) (by simp [srOff])
    · exact Offset.contains b (by simp [srOff]) (by simp [srOff]) (by simp [srOff])


theorem ginv_congr {to : Bool} {m₀ : Mem} {s₂ : State} {b S D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} {g : Nat} {s s' : State} (hi : GInv to m₀ s₂ b S D n R w icb g s)
    (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    GInv to m₀ s₂ b S D n R w icb g s' :=
  ⟨hi.hg, by rw [hg]; exact hi.rdx, fun ht => by rw [hm]; exact hi.slot ht, by rw [hg]; exact hi.r8,
    by rw [hg]; exact hi.base, by rw [hg]; exact hi.rdi, by rw [hg]; exact hi.rsp, by rw [hrd]; exact hi.rd,
    by rw [hwr]; exact hi.wr, by rw [hm]; exact hi.frame, by rw [hm]; exact hi.num, by rw [hm]; exact hi.data,
    by rw [hm]; exact hi.src⟩

/-- The loop over the groups: of four blocks or fewer when at most four are left, else of eight
or the last five to seven. -/
theorem groups_ok {to : Bool} {m₀ : Mem} {s₂ : State} {b S D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : GSetup to s₂ b S D n R w icb) (hmask : MasksAt s₂.mem b) {s : State}
    (hi : GInv to m₀ s₂ b S D n R w icb 0 s) :
    WP isa (.loop (groupG to) .ne) s (GDone m₀ s₂ b S D n R w icb) := by
  have hn := hs.hn
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 4 * g ∧ GInv to m₀ s₂ b S D n R w icb g s)
    (fun k s ⟨g, hk, hg⟩ => ?_) n s ⟨0, by omega_arith, hi⟩
  unfold groupG
  refine WP.seq (VG.Proof.Aes.X86_64.cmp_wp hg.r8 (by omega_arith) (K := 5) (by decide)
    fun s₁ cf₁ g₁ m₁ rd₁ wr₁ => ?_)
  have hg₁ := ginv_congr hg g₁ m₁ rd₁ wr₁
  have hlt := hg.hg
  refine WP.ite (decide (n - 4 * g < 5)) (by simp [X86_64.eval, cf₁]) (fun _ => ?_) (fun hb => ?_)
  · refine WP.mono (VG.Proof.Aes.X86_64.group_ok hs hg₁) fun s' h => ?_
    rcases h with ⟨z, d⟩ | ⟨z, d⟩
    · exact .inl ⟨by simp [X86_64.eval, z], d⟩
    · exact .inr ⟨by simp [X86_64.eval, z], n - 4 * (g + 1), by omega_arith, g + 1, rfl, d⟩
  · have h5 : 4 * g + 4 < n := by simp at hb; omega_arith
    refine WP.mono (sseGroup_ok hs hmask hg₁ h5) fun s' h => ?_
    rcases h with ⟨z, d⟩ | ⟨z, d⟩
    · exact .inl ⟨by simp [X86_64.eval, z], d⟩
    · exact .inr ⟨by simp [X86_64.eval, z], n - 4 * (g + 2), by omega_arith, g + 2, rfl, d⟩

end VG.Proof.Aes.X86_64.Sse

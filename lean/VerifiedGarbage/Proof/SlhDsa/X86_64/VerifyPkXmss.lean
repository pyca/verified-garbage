module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkChain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsGroup

/-!
# SLH-DSA on x86-64: `xmssPk`

`xmssPk` (`Impl/SlhDsa/X86_64/Verify.lean`) computes `xmssPkFromSig`
(Algorithm 11): its prologue (the registers saved in frame 1, the WOTS⁺
digits of the message at `oMsg`, `digits_eq`), the groups of chains
(`groupLoop_ok`), the WOTS⁺ public key (`wotsPk_ok`), the authentication
path (`pathLoop_ok`), and its epilogue (the root to `oMsg`, the registers
back).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs saveRegs restoreRegs)
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Spec.SlhDsa
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_store ea_at)
open VG.Proof.SlhDsa.X86_64.Levels (sx_ofNat add_add in_scr in_scr' at_add)

/-! ## The digits -/

theorem getD_app_l {l l' : List Nat} {i : Nat} (h : i < l.length) : (l ++ l').getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_r {l l' : List Nat} {i : Nat} (h : l.length ≤ i) :
    (l ++ l').getD i 0 = l'.getD (i - l.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem nibbles_length (X : List Byte) (n : Nat) : (nibbles X n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [nibbles] at ih ⊢
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil]
    omega

/-- Digit `c` of the nibbles: the high half of byte `c / 2` for an even `c`,
the low half for an odd one. -/
theorem nibbles_getD (X : List Byte) {n c : Nat} (hc : c < 2 * n) :
    (nibbles X n).getD c 0 =
      if c % 2 = 0 then (X.getD (c / 2) 0).toNat / 16 else (X.getD (c / 2) 0).toNat % 16 := by
  induction n with
  | zero => omega
  | succ n ih =>
    have e : nibbles X (n + 1) = nibbles X n ++ [(X.getD n 0).toNat / 16, (X.getD n 0).toNat % 16] := by
      simp only [nibbles]
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [e]
    by_cases h : c < 2 * n
    · rw [getD_app_l (by rw [nibbles_length]; exact h), ih h]
    · rw [getD_app_r (by rw [nibbles_length]; omega), nibbles_length]
      have h2 : c - 2 * n = 0 ∨ c - 2 * n = 1 := by omega
      rcases h2 with h2 | h2
      · rw [h2, ite_eq_left (by omega), show c / 2 = n by omega]; rfl
      · rw [h2, ite_eq_right (by omega), show c / 2 = n by omega]; rfl

/-- The checksum's sum, `Σ (15 - digit)` over the nibbles of the message,
as `Xmss.digits` computes it: `30n − dsum`. -/
theorem nibbles_csum (m : Mem) (S : Addr) (M : List Byte) {N : Nat}
    (hM : ∀ b < N, (M.getD b 0).toNat = msgByte m S b) :
    ∀ n ≤ N, ((nibbles M n).map (fun mi => 15 - mi)).sum = 30 * n - dsum m S n := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : nibbles M (n + 1) = nibbles M n ++ [(M.getD n 0).toNat / 16, (M.getD n 0).toNat % 16] := by
      simp only [nibbles]
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [e, List.map_append, List.sum_append, ih (by omega), hM n (by omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dsum]
    have := dsum_le m S n
    have := (m (S + BitVec.ofNat 64 (Layout.oMsg + n))).isLt
    simp only [msgByte] at *
    omega

theorem frame_dmem (m : Mem) (S : Addr) : ∀ b, b ≤ 64 → Frame [⟨at' S Layout.oDigits, 128⟩] m (dmem m S b)
  | 0, _ => Frame.refl _ _
  | b + 1, hb => by
    have e : Layout.oDigits = 30368 := rfl
    simp only [dmem]
    refine ((frame_dmem m S b (by omega)).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
    · show Region.Contains _ _ (8 / 8)
      exact Offset.contains S (by omega) (by omega) (by omega)
    · show Region.Contains _ _ (8 / 8)
      exact Offset.contains S (by omega) (by omega) (by omega)

/-- `len = 2n + 3` for `lg_w = 4`. -/
theorem len_eq (p : Params) (hw : p.lgw = 4) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) : p.len = 2 * p.n + 3 := by
  have h1 : p.len1 = 2 * p.n := by simp only [Params.len1, hw]; omega
  have h2 : p.len2 = 3 := by
    simp only [Params.len2, genLen2Loop_eq, Params.len1, Params.w, hw]
    rcases hn with h | h | h <;> rw [h] <;> decide
  simp only [Params.len, h1, h2]

/-- A byte the 64-bit write at `a` leaves. -/
theorem w64_other (m : Mem) (S : Addr) {o a : Nat} (v : BitVec 64) (ho : o < 2 ^ 16) (ha : a + 8 ≤ 2 ^ 16)
    (h : o + 1 ≤ a ∨ a + 8 ≤ o) : (m.writeW (at' S a) v) (at' S o) = m (at' S o) :=
  frame_at (frame_writeW m (at' S a) v) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint S (by omega) (by omega) (by omega)

/-- A byte the byte write at `a` leaves. -/
theorem w8_other (m : Mem) (S : Addr) {o a : Nat} (v : Byte) (ho : o < 2 ^ 16) (ha : a < 2 ^ 16) (h : o ≠ a) :
    (m.writeW (at' S a) v) (at' S o) = m (at' S o) :=
  writeB_other m v (ne_off S ho ha h)

/-- The WOTS⁺ digits `Xmss.digits` leaves at `oDigits`, those of the `n`
bytes at `oMsg` (`wotsDigits`). -/
theorem digits_val (p : Params) (hw : p.lgw = 4) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (m : Mem) (S : Addr) :
    ∀ c < p.len, ((csumMem (dmem m S p.n) S p.n (15 * 2 * p.n - dsum m S p.n)) (at' S (Layout.oDigits + c))).toNat =
      (wotsDigits p (bytesAt m (at' S Layout.oMsg) p.n)).getD c 0 := by
  intro c hc
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hl := len_eq p hw hn
  have eD : Layout.oDigits = 30368 := rfl
  have eV : ∀ i, Layout.oVar 1 i = 2576 + 8 * i := fun i => rfl
  rw [wotsDigits_eq p hw hn]
  simp only [csumMem]
  -- the two variables' writes
  rw [w64_other _ S _ (by rw [eD]; omega) (by rw [eV]; omega) (by rw [eD, eV]; omega),
    w64_other _ S _ (by rw [eD]; omega) (by rw [eV]; omega) (by rw [eD, eV]; omega)]
  by_cases h : c < 2 * p.n
  · rw [w8_other _ S _ (by rw [eD]; omega) (by rw [eD]; omega) (by omega),
      w8_other _ S _ (by rw [eD]; omega) (by rw [eD]; omega) (by omega),
      w8_other _ S _ (by rw [eD]; omega) (by rw [eD]; omega) (by omega), at', dmem_digit m S p.n (by omega) c h,
      getD_app_l (by rw [nibbles_length]; exact h), nibbles_getD _ h, bytesAt_getD _ _ (by omega), add_add]
    have hlt : nibD m S c < 256 := by
      have := (m (S + BitVec.ofNat 64 (Layout.oMsg + c / 2))).isLt
      simp only [nibD, msgByte]; split <;> omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    simp only [nibD, msgByte]
  · rw [getD_app_r (by rw [nibbles_length]; omega), nibbles_length,
      nibbles_csum m S _ (N := p.n) (fun b hb => by rw [bytesAt_getD _ _ hb, add_add]; rfl) p.n (Nat.le_refl _)]
    have h3 : c - 2 * p.n = 0 ∨ c - 2 * p.n = 1 ∨ c - 2 * p.n = 2 := by omega
    have hcs : 15 * 2 * p.n - dsum m S p.n = 30 * p.n - dsum m S p.n := by omega
    rw [hcs]
    rcases h3 with h3 | h3 | h3
    · rw [w8_other _ S _ (by rw [eD]; omega) (by rw [eD]; omega) (by omega),
        w8_other _ S _ (by rw [eD]; omega) (by rw [eD]; omega) (by omega),
        show Layout.oDigits + c = Layout.oDigits + 2 * p.n by omega, at', writeB_self, h3, BitVec.toNat_ofNat]
      simp only [csumDigits, List.getD_cons_zero]
      omega
    · rw [w8_other _ S _ (by rw [eD]; omega) (by rw [eD]; omega) (by omega),
        show Layout.oDigits + c = Layout.oDigits + 2 * p.n + 1 by omega, at', writeB_self, h3, BitVec.toNat_ofNat]
      simp only [csumDigits, List.getD_cons_succ, List.getD_cons_zero]
      omega
    · rw [show Layout.oDigits + c = Layout.oDigits + 2 * p.n + 2 by omega, at', writeB_self, h3, BitVec.toNat_ofNat]
      simp only [csumDigits, List.getD_cons_succ, List.getD_cons_zero]
      omega

/-- What `Xmss.digits` changes: the digits and the frame's variables 0 and 1. -/
theorem digits_frame (p : Params) (hn : p.n ≤ 32) (m : Mem) (S : Addr) (cs : Nat) :
    Frame [⟨at' S Layout.oDigits, 128⟩, ⟨at' S (Layout.oVar 1 0), 16⟩] m (csumMem (dmem m S p.n) S p.n cs) := by
  have eD : Layout.oDigits = 30368 := rfl
  have eV : ∀ i, Layout.oVar 1 i = 2576 + 8 * i := fun i => rfl
  have hd : Frame [⟨at' S Layout.oDigits, 128⟩, ⟨at' S (Layout.oVar 1 0), 16⟩] m (dmem m S p.n) :=
    (frame_dmem m S p.n (by omega)).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
  simp only [csumMem]
  have hD : ∀ i, i < 3 → Region.Contains ⟨at' S Layout.oDigits, 128⟩ (S + BitVec.ofNat 64 (Layout.oDigits + 2 * p.n + i)) (8 / 8) :=
    fun i hi => Offset.contains S (by omega) (by rw [eD]; omega) (by rw [eD]; omega)
  refine ((((hd.writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_self ..) _ ?_).writeW
    (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ ?_).writeW
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ ?_
  · have := hD 0 (by decide); rwa [Nat.add_zero] at this
  · exact hD 1 (by decide)
  · exact hD 2 (by decide)
  · exact Offset.contains S (by simp only [eV]; omega) (by simp only [eV]; omega) (by simp only [eV]; omega)
  · exact Offset.contains S (by simp only [eV]; omega) (by simp only [eV]; omega) (by simp only [eV]; omega)

/-! ## Bytes as lists -/

theorem bytesAt_add' (m : Mem) (a : Addr) (x y : Nat) :
    bytesAt m a (x + y) = bytesAt m a x ++ bytesAt m (a + BitVec.ofNat 64 x) y := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc, BitVec.ofNat_add]

theorem bytesAt_take (m : Mem) (a : Addr) {k n : Nat} (h : k ≤ n) : (bytesAt m a n).take k = bytesAt m a k := by
  rw [show n = k + (n - k) by omega, bytesAt_add', List.take_left' (bytesAt_length' _ _ _)]

theorem bytesAt_drop (m : Mem) (a : Addr) (k l : Nat) :
    (bytesAt m a (k + l)).drop k = bytesAt m (a + BitVec.ofNat 64 k) l := by
  rw [bytesAt_add', List.drop_left' (bytesAt_length' _ _ _)]

/-- `c` strings of `n` bytes. -/
theorem bytesAt_chunks (m : Mem) (a : Addr) (n : Nat) :
    ∀ c, bytesAt m a (c * n) = (List.range c).flatMap fun i => bytesAt m (a + BitVec.ofNat 64 (i * n)) n
  | 0 => by simp [bytesAt]
  | c + 1 => by
    rw [Nat.succ_mul, bytesAt_add', bytesAt_chunks m a n c, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

/-! ## The prologue and the epilogue -/

theorem oSave1 (i : Nat) : Layout.oSave 1 i = 2528 + 8 * i := rfl

/-- After `xpro`. -/
structure XPro (s t : State) : Prop where
  bx : t.gpr .rbx = s.gpr .rdi
  r12 : t.gpr .r12 = s.gpr .rsi
  r13 : t.gpr .r13 = s.gpr .rdx
  r14 : t.gpr .r14 = s.gpr .rdi + BitVec.ofNat 64 Layout.oMsg
  r15 : t.gpr .r15 = s.gpr .rdi + BitVec.ofNat 64 Layout.oMsg
  sp : t.gpr .rsp = s.gpr .rsp
  rbp : t.gpr .rbp = s.gpr .rbp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  saved : ∀ i < 6, t.mem.readW (at' (s.gpr .rdi) (Layout.oSave 1 i)) 64 = s.gpr (savedRegs.getD i .rbx)
  frame : Frame [⟨at' (s.gpr .rdi) (Layout.oSave 1 0), 48⟩] s.mem t.mem

theorem xpro_ok {s : State} (hw : (⟨s.gpr .rdi, 2 ^ 16⟩ : Region) ∈ s.wr) :
    WP isa (.block Impl.SlhDsa.X86_64.Verify.xpro) s (XPro s) := by
  have hc : ∀ j < 6, Region.Contains ⟨at' (s.gpr .rdi) (Layout.oSave 1 0), 48⟩ (at' (s.gpr .rdi) (2528 + 8 * j)) 8 :=
    fun j hj => by
      rw [oSave1, show at' (s.gpr .rdi) (2528 + 8 * j) = at' (s.gpr .rdi) (2528 + 8 * 0) + BitVec.ofNat 64 (8 * j) by
        rw [at_add]]
      exact Offset.contains_base _ (by omega) (by omega)
  unfold Impl.SlhDsa.X86_64.Verify.xpro
  refine WP.block_append (WP.mono (Levels.wp_rangeMap (P := fun j t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ i < j, t.mem.readW (at' (s.gpr .rdi) (Layout.oSave 1 i)) 64 = s.gpr (savedRegs.getD i .rbx)) ∧
      Frame [⟨at' (s.gpr .rdi) (Layout.oSave 1 0), 48⟩] s.mem t.mem) 6
    ⟨rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩ fun j hj t ⟨g, r, w, sv, f⟩ => ?_) fun t ht => ?_)
  · refine wp_store (a := at' (s.gpr .rdi) (Layout.oSave 1 j)) (by rw [ea_at, g]) (by
      rw [w, oSave1]; exact in_scr hw (by omega)) fun t' g' m' r' w' => WP.block_nil ?_
    refine ⟨by rw [g', g], by rw [r', r], by rw [w', w], fun i hi => ?_, ?_⟩
    · rw [m']
      by_cases e : i = j
      · subst e; rw [Mem.readW_writeW_self64, g]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by rw [oSave1, oSave1]; omega) (by rw [oSave1]; omega)
          (by rw [oSave1]; omega)) (by decide), sv i (by omega)]
    · rw [m']
      exact f.writeW (List.mem_singleton_self _) _ (by rw [oSave1]; exact hc j (by omega))
  obtain ⟨g, r, w, sv, f⟩ := ht
  refine wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => wp_mov fun t₃ u₃ => wp_mov fun t₄ u₄ => wp_addi fun t₅ u₅ => ?_
  refine wp_mov fun t₆ u₆ => WP.block_nil ?_
  have hm₆ : t₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have h15 : t₅.gpr .r15 = s.gpr .rdi + BitVec.ofNat 64 Layout.oMsg := by
    rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g,
      sx_ofNat (by rw [show Layout.oMsg = 30496 from rfl]; omega)]
  refine ⟨?_, ?_, ?_, by rw [u₆.gpr, h15], by rw [u₆.other _ (by decide), h15], ?_,
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), g],
    by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, r], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, w],
    fun i hi => by rw [hm₆]; exact sv i hi, by rw [hm₆]; exact f⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, g]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), g]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), g]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), g]

/-- The epilogue's registers: the callee-saved registers from frame 1. -/
theorem restore1_ok {σ t : State} {S : Addr} (hbx : t.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr)
    (hsv : ∀ i < 6, t.mem.readW (at' S (Layout.oSave 1 i)) 64 = σ.gpr (savedRegs.getD i .rbx))
    (hsp : t.gpr .rsp = σ.gpr .rsp) {Q : State → Prop}
    (k : ∀ t', t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → (∀ r ∈ calleeSaved, t'.gpr r = σ.gpr r) → Q t') :
    WP isa (.block (restoreRegs 1)) t Q := by
  have hin : ∀ (u : State), u.rd = t.rd → u.wr = t.wr → ∀ i < 6, InRegions (u.rd ++ u.wr) (at' S (Layout.oSave 1 i)) 8 :=
    fun u hr hw' i hi => by rw [hr, hw']; exact in_scr' hw (by rw [oSave1]; omega)
  rw [show restoreRegs 1 = [Instr.mov .r15 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 1 5))),
    .mov .r14 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 1 4))), .mov .r13 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 1 3))),
    .mov .r12 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 1 2))), .mov .rbp (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 1 1))),
    .mov .rbx (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 1 0)))] from rfl]
  refine wp_movm (by rw [ea_at, hbx]) (hin t rfl rfl 5 (by decide)) fun t₁ u₁ => ?_
  refine wp_movm (by rw [ea_at, u₁.other _ (by decide), hbx]) (hin _ u₁.rd u₁.wr 4 (by decide)) fun t₂ u₂ => ?_
  refine wp_movm (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) 3 (by decide)) fun t₃ u₃ => ?_
  refine wp_movm (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr]) 2 (by decide)) fun t₄ u₄ => ?_
  refine wp_movm (by rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 1 (by decide)) fun t₅ u₅ => ?_
  refine wp_movm (by rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 0 (by decide))
    fun t₆ u₆ => WP.block_nil ?_
  have hm₁ : t₁.mem = t.mem := u₁.mem
  have hm₂ : t₂.mem = t.mem := by rw [u₂.mem, hm₁]
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, hm₂]
  have hm₄ : t₄.mem = t.mem := by rw [u₄.mem, hm₃]
  have hm₅ : t₅.mem = t.mem := by rw [u₅.mem, hm₄]
  refine k t₆ (by rw [u₆.mem, hm₅]) (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) fun r hr => ?_
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [u₆.gpr, hm₅]; exact hsv 0 (by decide)
  · rw [u₆.other _ (by decide), u₅.gpr, hm₄]; exact hsv 1 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hsp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hm₃]; exact hsv 2 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hm₂]
    exact hsv 3 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hm₁]
    exact hsv 4 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
    exact hsv 5 (by decide)

theorem wotsDigits_lt (p : Params) (hw : p.lgw = 4) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (M : List Byte) (c : Nat) :
    (wotsDigits p M).getD c 0 < 16 := by
  rw [wotsDigits_eq p hw hn]
  by_cases h : c < 2 * p.n
  · rw [getD_app_l (by rw [nibbles_length]; exact h), nibbles_getD _ h]
    have := (M.getD (c / 2) 0).isLt
    split <;> omega
  · rw [getD_app_r (by rw [nibbles_length]; omega), nibbles_length]
    generalize c - 2 * p.n = i
    generalize ((nibbles M p.n).map (fun mi => 15 - mi)).sum = cs
    simp only [csumDigits]
    rcases i with _ | _ | _ | i
    · simp only [List.getD_cons_zero]; omega
    · simp only [List.getD_cons_succ, List.getD_cons_zero]; omega
    · simp only [List.getD_cons_succ, List.getD_cons_zero]; omega
    · simp only [List.getD_cons_succ, List.getD_nil]; omega

/-- The memory after `xmssPk`'s prologue (`xpro`, the digits, variable 0
zeroed). -/
structure XProMem (p : Params) (s : State) (S : Addr) (t : State) : Prop where
  bx : t.gpr .rbx = S
  r12 : t.gpr .r12 = s.gpr .rsi
  r13 : t.gpr .r13 = s.gpr .rdx
  r14 : t.gpr .r14 = S + BitVec.ofNat 64 Layout.oMsg
  cs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  saved : ∀ i < 6, t.mem.readW (at' S (Layout.oSave 1 i)) 64 = s.gpr (savedRegs.getD i .rbx)
  v0 : t.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 0
  digits : ∀ c < p.len, (t.mem (at' S (Layout.oDigits + c))).toNat =
    (wotsDigits p (bytesAt s.mem (at' S Layout.oMsg) p.n)).getD c 0
  frame : Frame [⟨at' S (Layout.oSave 1 0), 48⟩, ⟨at' S Layout.oDigits, 128⟩, ⟨at' S (Layout.oVar 1 0), 16⟩] s.mem t.mem

/-- `xmssPk`'s prologue. -/
theorem xpre_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hw4 : p.lgw = 4) {s : State}
    (hw : (⟨s.gpr .rdi, 2 ^ 16⟩ : Region) ∈ s.wr) :
    WP isa (.block (Impl.SlhDsa.X86_64.Verify.xpro ++ Impl.SlhDsa.X86_64.Xmss.digits (Impl.SlhDsa.X86_64.Shake.layout p) ++
      ([.mov32 .rax (.imm 0), .store (Impl.SlhDsa.X86_64.Verify.xv 0) .rax] : List Instr))) s (XProMem p s (s.gpr .rdi)) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eD : Layout.oDigits = 30368 := rfl
  have eM : Layout.oMsg = 30496 := rfl
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (xpro_ok hw) fun t ht => ?_)
  have hwt : (⟨s.gpr .rdi, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [ht.wr]; exact hw
  refine digits_ok (Impl.SlhDsa.X86_64.Shake.layout p) hn32 (S := s.gpr .rdi) ht.bx ht.r15
    (fun o ho => in_scr hwt ho) (fun o ho => in_scr hwt ho) (fun o ho => in_scr' hwt ho)
    fun s₁ hm₁ g₁ r₁ w₁ => ?_
  refine wp_mov32i fun s₂ u₂ => wp_store (a := at' (s.gpr .rdi) (Layout.oVar 1 0))
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, ea_at, u₂.other _ (by decide), g₁ _ (by decide) (by decide) (by decide)
      (by decide), ht.bx])
    (by rw [u₂.wr, w₁, ht.wr, oVar10]; exact in_scr hw (by omega)) fun s₃ g₃ m₃ r₃ w₃ => WP.block_nil ?_
  have hm₃ : s₃.mem = s₁.mem.writeW (at' (s.gpr .rdi) (Layout.oVar 1 0)) (BitVec.ofNat 64 0) := by
    rw [m₃, u₂.gpr, u₂.mem]; rfl
  -- the message, which the registers' stores leave
  have hmsg : bytesAt t.mem (at' (s.gpr .rdi) Layout.oMsg) p.n = bytesAt s.mem (at' (s.gpr .rdi) Layout.oMsg) p.n :=
    bytesAt_frame ht.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [oSave1]; exact Offset.disjoint _ (by rw [eM]; omega) (by rw [eM]; omega) (by omega)) (by omega)
  have hg : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .r10 → g ≠ .r11 → s₃.gpr g = t.gpr g := fun g h1 h2 h3 h4 => by
    rw [g₃, u₂.other _ h1, g₁ _ h1 h2 h3 h4]
  refine ⟨by rw [hg _ (by decide) (by decide) (by decide) (by decide), ht.bx],
    by rw [hg _ (by decide) (by decide) (by decide) (by decide), ht.r12],
    by rw [hg _ (by decide) (by decide) (by decide) (by decide), ht.r13],
    by rw [hg _ (by decide) (by decide) (by decide) (by decide), ht.r14], fun r hr h1 h2 h3 h4 h5 => ?_,
    by rw [r₃, u₂.rd, r₁, ht.rd], by rw [w₃, u₂.wr, w₁, ht.wr], fun i hi => ?_,
    by rw [hm₃, Mem.readW_writeW_self64], fun c hc => ?_, ?_⟩
  · have h' : r = .rbp ∨ r = .rsp := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    rcases h' with rfl | rfl
    · rw [hg _ (by decide) (by decide) (by decide) (by decide), ht.rbp]
    · rw [hg _ (by decide) (by decide) (by decide) (by decide), ht.sp]
  · have F := digits_frame p hn32 t.mem (s.gpr .rdi) (15 * 2 * p.n - dsum t.mem (s.gpr .rdi) p.n)
    rw [hm₃, Mem.readW_writeW_sep (Offset.sep _ (by rw [oSave1, oVar10]; omega) (by rw [oSave1]; omega)
      (by rw [oVar10]; omega)) (by decide), hm₁]
    have e := F.readW (r := ⟨at' (s.gpr .rdi) (Layout.oSave 1 i), 8⟩) (a := at' (s.gpr .rdi) (Layout.oSave 1 i))
      (w := 64) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [oSave1]; exact Offset.disjoint _ (by rw [eD]; omega) (by omega) (by rw [eD]; omega)
        · rw [oSave1, oVar10]; exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
    exact e.trans (ht.saved i hi)
  · have hl := len_eq p hw4 hn
    rw [hm₃, w64_other _ _ _ (by rw [eD]; omega) (by rw [oVar10]; omega) (by rw [eD, oVar10]; omega), hm₁, ← hmsg]
    exact digits_val p hw4 hn t.mem (s.gpr .rdi) c hc
  · have F := digits_frame p hn32 t.mem (s.gpr .rdi) (15 * 2 * p.n - dsum t.mem (s.gpr .rdi) p.n)
    rw [hm₁] at hm₃
    refine (ht.frame.mono fun r hr => ?_).trans ((F.mono fun r hr => ?_).trans ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp
    · rw [hm₃]
      exact (Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _
        (Offset.contains _ (Nat.le_refl _) (by decide) (by rw [oVar10]; omega))

theorem flatMap_range_congr {f g : Nat → List Byte} : ∀ {n : Nat}, (∀ i < n, f i = g i) →
    (List.range n).flatMap f = (List.range n).flatMap g
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, flatMap_range_congr (fun i hi => h i (by omega)),
      List.flatMap_singleton, List.flatMap_singleton, h n (by omega)]

/-- `Env` determines `PK.seed` and `a16`. -/
theorem Env.unique {p : Params} {m : Mem} {S : Addr} {pk pk' a a' : List Byte}
    (h : Env p m S pk a) (h' : Env p m S pk' a') : pk' = pk ∧ a' = a :=
  ⟨by rw [← h'.seedA 0 (by decide), h.seedA 0 (by decide)], by rw [← h'.adrsA 0 (by decide), h.adrsA 0 (by decide)]⟩

/-- `xmssPk`, from a state that meets `xmssPkContract`'s precondition: its
postcondition, with the callee-saved registers as they were. -/
theorem xmssPk_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (hw4 : p.lgw = 4)
    (hhp : 0 < p.hp) (hhp' : p.hp ≤ 32) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {s : State} (hpre : (xmssPkContract p stack).pre s) :
    WP isa (Impl.SlhDsa.X86_64.Verify.xmssPk p f) s (fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ (xmssPkContract p stack).post s s') := by
  obtain ⟨R, ⟨pkSeed, a16, henv⟩, hidx⟩ := hpre
  obtain ⟨S, hS0⟩ : ∃ S, S = s.gpr .rdi := ⟨_, rfl⟩
  obtain ⟨sig, hsig0⟩ : ∃ sig, sig = s.gpr .rdx := ⟨_, rfl⟩
  obtain ⟨idx, hidx0⟩ : ∃ idx, idx = (s.gpr .rsi).toNat := ⟨_, rfl⟩
  rw [← hS0] at R henv; rw [← hsig0] at R; rw [← hidx0] at hidx
  show WP isa _ s fun s' => _ ∧ ∀ pkSeed a16, Env p s.mem (s.gpr .rdi) pkSeed a16 → _
  rw [← hS0, ← hsig0, ← hidx0]
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hl := len_eq p hw4 hn
  have hlen1 : 1 ≤ p.len := by omega
  have hlen : p.len ≤ 128 := by omega
  have hlB : p.n + 32 + p.len * p.n ≤ Layout.strideB := by
    rw [hl, show Layout.strideB = 2208 from rfl]; rcases hn with h | h | h <;> rw [h] <;> decide
  have hlen31 : p.len * p.n < 2 ^ 31 := by rw [hl]; rcases hn with h | h | h <;> rw [h] <;> decide
  have hidx32 : idx < 2 ^ 32 := Nat.lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) hhp')
  have hxs : p.xmssSigLen = p.len * p.n + p.hp * p.n := by simp only [Params.xmssSigLen, Nat.add_mul]
  have hsL : p.len * p.n ≤ p.xmssSigLen := by omega
  have ha16 : a16.length = 16 := by rw [← henv.adrsA 0 (by decide)]; exact bytesAt_length' _ _ _
  have eA0 : Layout.laneA 0 = 3296 := rfl
  have eB0 : Layout.laneB 0 = 3808 := rfl
  have eM : Layout.oMsg = 30496 := rfl
  have eD : Layout.oDigits = 30368 := rfl
  -- the regions
  have hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr := by rw [R.wr_eq]; exact List.mem_cons_self ..
  have hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64 := R.scr_fit
  have hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩ := R.stk_scr
  have hsr : (⟨sig, p.xmssSigLen⟩ : Region) ∈ s.rd := by rw [R.rd_eq]; exact List.mem_singleton_self _
  have hsfit : sig.toNat + p.xmssSigLen ≤ 2 ^ 64 := R.rd_fit _ (by rw [← R.rd_eq]; exact hsr)
  have hss : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, 2 ^ 16⟩ := R.rd_scr _ (by rw [← R.rd_eq]; exact hsr)
  have hsb : Region.Disjoint ⟨sig, p.xmssSigLen⟩ (below (s.gpr .rsp) stack) :=
    (R.stk_rd _ (by rw [← R.rd_eq]; exact hsr)).symm
  -- what a frame in `scratch` and the stack leaves of the signature
  have hsigF : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' → (∀ r ∈ rs, Region.Disjoint ⟨sig, p.xmssSigLen⟩ r) →
      ∀ {o l : Nat}, o + l ≤ p.xmssSigLen →
        bytesAt m' (sig + BitVec.ofNat 64 o) l = bytesAt m (sig + BitVec.ofNat 64 o) l := fun hf hd o l hol =>
    bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub_base sig hol)) (by omega)
  -- the frame after the prologue
  obtain ⟨G, hG⟩ : ∃ G : List Region, G = xFrame p S (s.gpr .rsp) stack ++ [⟨at' S Layout.oMsg, 64⟩] := ⟨_, rfl⟩
  have hGc : ∀ r ∈ G, ∃ r' ∈ changes p S ++ [below (s.gpr .rsp) stack], Region.Sub r r' := fun r hr => by
    rw [hG] at hr
    rcases List.mem_append.mp hr with hr | hr
    · exact xFrame_sub p S _ stack r hr
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))))), fun _ h => h⟩
  have hGs : ∀ r ∈ G, Region.Disjoint ⟨sig, p.xmssSigLen⟩ r := fun r hr => by
    rw [hG] at hr
    rcases List.mem_append.mp hr with hr | hr
    · exact xFrame_disj' hn32 hss hsb r hr
    · rw [List.mem_singleton] at hr; subst hr; exact hss.sub_right (Offset.sub_base S (by rw [eM]; omega))
  have hGv : ∀ r ∈ G, Region.Disjoint ⟨at' S 2528, 48⟩ r := fun r hr => by
    rw [hG] at hr
    rcases List.mem_append.mp hr with hr | hr
    · exact xFrame_save hn32 hstk r hr
    · rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by rw [eM]; omega) (by omega) (by omega)
  have hchG : ∀ r ∈ chFrame p S (s.gpr .rsp) stack, ∃ r' ∈ G, Region.Sub r r' := fun r hr =>
    ⟨r, by rw [hG]; exact List.mem_append_left _ (List.mem_append_left _ hr), fun _ h => h⟩
  unfold Impl.SlhDsa.X86_64.Verify.xmssPk
  -- the prologue
  refine WP.seq (WP.mono (xpre_ok hn hw4 (by rw [← hS0]; exact hw)) fun s₂ h₂ => ?_)
  rw [← hS0] at h₂
  have hsp₂ : s₂.gpr .rsp = s.gpr .rsp := h₂.cs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have F₂c : Frame (changes p S ++ [below (s.gpr .rsp) stack]) s.mem s₂.mem := h₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
        Offset.sub S (by rw [oSave1]; simp only [Layout.oVars]; omega) (by rw [oSave1]; simp only [Layout.oVars]; omega)⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..)), fun _ h => h⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
        Offset.sub S (by rw [oVar10]; simp only [Layout.oVars]; omega) (by rw [oVar10]; simp only [Layout.oVars]; omega)⟩
  have henv₂ := Env.of_frame hn32 henv F₂c hstk
  have hsig₂ : ∀ {o l : Nat}, o + l ≤ p.xmssSigLen →
      bytesAt s₂.mem (sig + BitVec.ofNat 64 o) l = bytesAt s.mem (sig + BitVec.ofNat 64 o) l := fun hol =>
    hsigF h₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hss.sub_right (Offset.sub_base S (by rw [oSave1]; omega))
      · exact hss.sub_right (Offset.sub_base S (by rw [eD]; omega))
      · exact hss.sub_right (Offset.sub_base S (by rw [oVar10]; omega))) hol
  -- the chains
  have hD₂ : ∀ c < p.len, (s₂.mem (at' S (Layout.oDigits + c))).toNat ≤ 15 := fun c hc => by
    rw [h₂.digits c hc]; have := wotsDigits_lt p hw4 hn (bytesAt s.mem (at' S Layout.oMsg) p.n) c; omega
  refine WP.seq (groupLoop_ok T ht hn hfam hlen1 hlen hlB hst hs63 hidx32 h₂.bx
    (by rw [h₂.r12, hidx0, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [h₂.r13, hsig0]) h₂.v0 (by rw [h₂.wr]; exact hw) hS
    (by rw [hsp₂]; exact hstk) henv₂ (by rw [h₂.rd]; exact hsr) hsfit hss hsL (by rw [hsp₂]; exact hsb) hD₂
    fun s₃ g₃ r₃ w₃ e₃ F₃ => ?_)
  rw [hsp₂] at F₃
  have F₃G : Frame G s₂.mem s₃.mem := F₃.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hchG r hr
    · rw [List.mem_singleton] at hr; subst hr
      refine ⟨_, by rw [hG]; exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨0, List.mem_range.mpr (by decide), rfl⟩)), Offset.sub S (by omega) ?_⟩
      have : p.n + 32 + p.len * p.n ≤ 2208 := hlB
      omega
  have hsp₃ : s₃.gpr .rsp = s.gpr .rsp := by rw [g₃ _ (by decide), hsp₂]
  have henv₃ := Env.of_frame hn32 henv₂ (F₃G.sub hGc) hstk
  -- the public key
  refine WP.seq (wotsPk_ok T ht hn hfam hlB hst hs63 hidx32 (by rw [g₃ _ (by decide), h₂.bx])
    (by rw [g₃ _ (by decide), h₂.r12, hidx0, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [w₃, h₂.wr]; exact hw) hS
    (by rw [hsp₃]; exact hstk) henv₃ fun s₄ g₄ r₄ w₄ v₄ F₄ => ?_)
  rw [hsp₃] at F₄
  have F₄G : Frame G s₃.mem s₄.mem := F₄.sub fun r hr => ⟨r, by rw [hG]; exact List.mem_append_left _ hr, fun _ h => h⟩
  have hsp₄ : s₄.gpr .rsp = s.gpr .rsp := by rw [g₄ _ (by decide), hsp₃]
  have hb₄ : s₄.gpr .rbx = S := by rw [g₄ _ (by decide), g₃ _ (by decide), h₂.bx]
  -- variable 3 ← 0
  refine WP.seq (wp_mov32i fun s₅ u₅ => wp_store (a := at' S (Layout.oVar 1 3))
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, ea_at, u₅.other _ (by decide), hb₄])
    (by rw [u₅.wr, w₄, w₃, h₂.wr, oVar13]; exact in_scr hw (by omega)) fun s₆ g₆ m₆ r₆ w₆ => WP.block_nil ?_)
  have hm₆ : s₆.mem = s₄.mem.writeW (at' S (Layout.oVar 1 3)) (BitVec.ofNat 64 0) := by rw [m₆, u₅.gpr, u₅.mem]; rfl
  have hg₆ : ∀ r, r ≠ .rax → s₆.gpr r = s₄.gpr r := fun r h => by rw [g₆, u₅.other _ h]
  have F₆G : Frame G s₄.mem s₆.mem := by
    rw [hm₆]
    refine (frame_writeW _ _ _).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨r', h', hs'⟩ := sub_ch hn32 S (s.gpr .rsp) stack (o := Layout.oVar 1 3) (l := 64 / 8)
      (Or.inr (Or.inr (Or.inr ⟨by rw [oVar13]; omega, by rw [oVar13]⟩)))
    obtain ⟨r'', h'', hs''⟩ := hchG r' h'
    exact ⟨r'', h'', fun x hx => hs'' x (hs' x hx)⟩
  have F₂₆ : Frame G s₂.mem s₆.mem := F₃G.trans (F₄G.trans F₆G)
  have henv₆ := Env.of_frame hn32 henv₂ (F₂₆.sub hGc) hstk
  have hcs₆ : ∀ r ∈ calleeSaved, s₆.gpr r = s₂.gpr r := fun r hr => by
    have : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hg₆ r this, g₄ r hr, g₃ r hr]
  have hsp₆ : s₆.gpr .rsp = s.gpr .rsp := by rw [hcs₆ _ (by decide), hsp₂]
  have hw₆ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₆.wr := by rw [w₆, u₅.wr, w₄, w₃, h₂.wr]; exact hw
  -- the authentication path
  refine WP.seq (pathLoop_ok T ht hn hfam hlen31 hhp (by omega) hst hs63 hidx32
    (by rw [hcs₆ _ (by decide), h₂.bx]) (by rw [hcs₆ _ (by decide), h₂.r12, hidx0, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by rw [hcs₆ _ (by decide), h₂.r13, hsig0]) (by rw [hm₆, Mem.readW_writeW_self64]) hw₆ hS
    (by rw [hsp₆]; exact hstk) henv₆ (by rw [r₆, u₅.rd, r₄, r₃, h₂.rd]; exact hsr) hsfit hss
    (by rw [hsp₆]; exact hsb) fun s₇ g₇ r₇ w₇ l₇ F₇ => ?_)
  rw [hsp₆] at F₇
  have F₂₇ : Frame G s₂.mem s₇.mem := F₂₆.trans (F₇.sub hchG)
  -- the root to `oMsg`, the registers back
  have hmsg : (Impl.SlhDsa.X86_64.Shake.layout p).msgOff = p.n + 32 := rfl
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  rw [hmsg]
  have hw₇ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₇.wr := by rw [w₇]; exact hw₆
  refine WP.block_append (WP.mono (Levels.copy_ok (S := S) (t := .r14) (sr := .rbx) (by decide) (by decide)
    (a := Layout.oMsg) (b := 0) (d₁ := Layout.laneA 0 + (p.n + 32)) (d₂ := 0) (p.n / 8) s₇
    (by rw [g₇ _ (by decide), hcs₆ _ (by decide), h₂.r14])
    (by rw [g₇ _ (by decide), hcs₆ _ (by decide), h₂.bx]; exact Levels.scr0 S) hw₇ (by omega) (by omega)
    (by omega)) fun s₈ ⟨g₈, r₈, w₈, c₈, f₈⟩ => ?_)
  have F₂₈ : Frame G s₂.mem s₈.mem := F₂₇.trans (f₈.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by rw [hG]; exact List.mem_append_right _ (List.mem_singleton_self _),
      Offset.sub S (by omega) (by rw [e8]; omega)⟩)
  have hbx₈ : s₈.gpr .rbx = S := by rw [g₈ _ (by decide), g₇ _ (by decide), hcs₆ _ (by decide), h₂.bx]
  refine restore1_ok (σ := s) hbx₈ (by rw [w₈]; exact hw₇) (fun i hi => ?_)
    (by rw [g₈ _ (by decide), g₇ _ (by decide), hsp₆]) fun s₉ m₉ r₉ w₉ cs₉ => ⟨cs₉, fun pk' a' henv' => ?_⟩
  · rw [F₂₈.readW (r := ⟨at' S 2528, 48⟩) (Offset.contains S (by rw [oSave1]; omega) (by rw [oSave1]; omega)
      (by omega)) hGv (by decide)]
    exact h₂.saved i hi
  obtain ⟨e₁, e₂⟩ := Env.unique henv henv'
  rw [e₁, e₂]
  have Ff : Frame (changes p S ++ [below (s.gpr .rsp) stack]) s.mem s₉.mem := by
    rw [m₉]; exact F₂c.trans (F₂₈.sub hGc)
  refine ⟨Env.of_frame hn32 henv Ff hstk, ?_, Ff⟩
  -- the root
  have hsig₆ : ∀ {o l : Nat}, o + l ≤ p.xmssSigLen →
      bytesAt s₆.mem (sig + BitVec.ofNat 64 o) l = bytesAt s.mem (sig + BitVec.ofNat 64 o) l := fun hol => by
    rw [hsigF F₂₆ hGs hol, hsig₂ hol]
  have hroot : bytesAt s₉.mem (at' S Layout.oMsg) p.n = bytesAt s₇.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n := by
    rw [m₉]
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have := c₈ i (by have := List.mem_range.mp hi; omega)
    rw [at', at', add_add, add_add, show Layout.oMsg + i = Layout.oMsg + 0 + i by omega, this,
      show 0 + (Layout.laneA 0 + (p.n + 32)) + i = Layout.laneA 0 + p.n + 32 + i by omega]
  have hpk₆ : bytesAt s₆.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n =
      bytesAt s₄.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n := by
    rw [hm₆]
    exact bytesAt_frame (frame_writeW _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [oVar13]; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by omega)
  rw [hroot, l₇, hpk₆, v₄, hsig₆ (by omega), xmssPkFromSig_eq p ha16 hidx32, wotsPkFromSig_eq p ha16 hidx32,
    hxs, bytesAt_drop, ← hxs, bytesAt_chunks s₃.mem (at' S (Layout.laneB 0 + p.n + 32)) p.n p.len]
  refine congrArg (path p pkSeed a16 2 0 idx _ p.hp) (congrArg (Spec.SlhDsa.T p pkSeed (adrsOf a16 1 idx 0 0)) ?_)
  refine flatMap_range_congr fun i hi => ?_
  have hin : i * p.n + p.n ≤ p.xmssSigLen := by
    have : i * p.n + p.n ≤ p.len * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    omega
  rw [at_add, e₃ i hi, h₂.digits i hi, bytesAt_take _ _ hsL, chunk_bytesAt _ _ hi, hsig₂ hin,
    show p.w - 1 = 15 by simp only [Params.w, hw4]]

end VG.Proof.SlhDsa.X86_64

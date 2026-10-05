import VerifiedGarbage.Impl.CmacAes.X86_64.AesNi
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract

/-!
# AES-CMAC's chaining with AES-NI on x86-64: `vg_cmac_aes_update_aesni_cbc`

The code reads everything it needs before it writes the state, once, at the
end, so the proof is about registers: after the setup, the round keys are in
their registers (`kreg`), `xmm15` holds `K_Nr ⊕ K₀`, and after `k` blocks
`xmm0 ⊕ K₀` is the chaining value of the first `k` blocks (`Inv`). Each
block (`body_ok`) is the cipher's first `AddRoundKey` (`pxor` of the block
into `xmm0`), its full rounds, composed by induction (`rounds_ok`), and its
last round, which leaves `CIPH_K(Cᵢ₋₁ ⊕ Mᵢ) ⊕ K₀` (`last_round`).

The proof is written against `cbcX86_64`, which asks less than the shared
contract with no stack (the code uses none) and than `updateX86_64`, the
contract callers of `vg_cmac_aes_update` are proven with
(`Proof/CmacAes/X86_64/Variant.lean`).
-/

namespace VG.Proof.CmacAes.X86_64.AesNi

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Aes.X86_64.AesNi (st st_ext getD_st byte_xor pxor_st aesenc_st aesenclast_st rnds
  rnds_zero rnds_succ cipher_eq byte_roundKey XFrame cmpRsi_ok)
open VG.Impl.CmacAes.X86_64.AesNi
open VG.Spec.Aes (roundKey cipher)

/-! ## The contract -/

/-- `vg_cmac_aes_update_aesni_cbc(schedule = rdi, rounds = rsi, state = rdx, data = rcx, n = r8,
scratch = r9)`: `updateX86_64` without the stack and the disjointness of the
buffers, which the code does not need. -/
def cbcX86_64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let state : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2176⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched, data] ∧ s.wr = [state, scr] ∧ ret.Disjoint state ∧
      (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 =
      Spec.Cmac.chain (ciphAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16)
        (Spec.Cmac.blocksAt s.mem (s.gpr .rcx) 16 (s.gpr .r8).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp

theorem pre_of_update {s : State} (h : updateX86_64.pre s) : cbcX86_64.pre s :=
  let ⟨a, b, _, _, _, _, _, c, _, _, _, _, _, _, d, _, e⟩ := h
  ⟨a, b, c, d, e⟩

/-- The precondition, by name. -/
structure CPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, dataR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (stR s₀)
  data_wrap : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem CPre.of {s₀ : State} (h : cbcX86_64.pre s₀) : CPre s₀ :=
  let ⟨a, b, c, d, e⟩ := h
  ⟨a, b, c, d, e⟩

/-! ## Blocks in registers -/

/-- A register's 16 bytes, in memory order. -/
def bytes (v : BitVec 128) : List Byte := (st v).toList

theorem bytes_read (m : Mem) (p : Addr) : bytes (m.readW p 128) = Spec.Aes.bytesAt m p 16 := by
  apply List.ext_getElem
  · simp [bytes, Spec.Aes.bytesAt]
  · intro i hi _
    have hi' : i < 16 := by simpa [bytes] using hi
    simp only [bytes, st, Vector.getElem_toList, Vector.getElem_ofFn, Spec.Aes.bytesAt,
      List.getElem_map, List.getElem_range]
    exact VG.Proof.Gcm.X86_64.byte_readW m p hi'

theorem bytes_xor (a b : BitVec 128) : bytes (a ^^^ b) = Spec.Cmac.xor (bytes a) (bytes b) := by
  apply List.ext_getElem
  · simp [bytes, Spec.Cmac.xor]
  · intro i hi _
    simp [bytes, st, Spec.Cmac.xor, byte_xor]

theorem ofFn_bytes (v : BitVec 128) : (Vector.ofFn fun i : Fin 16 => (bytes v).getD i 0) = st v :=
  st_ext fun i hi => by simp [bytes, Vector.getD, hi]

/-- `CIPH_K` of a register's bytes. -/
theorem aesWith_bytes (nr : Nat) (w : List Byte) (v r : BitVec 128) (h : st r = cipher nr w (st v)) :
    Spec.Cmac.aesWith nr w (bytes v) = bytes r := by
  rw [Spec.Cmac.aesWith, ofFn_bytes, ← h]; rfl

theorem bytes_write (m : Mem) (p : Addr) (v : BitVec 128) :
    Spec.Aes.bytesAt (m.writeW p v) p 16 = bytes v := by
  rw [← bytes_read, Mem.readW_writeW_self _ _ 16 _ (by decide)]

/-! ## Round keys -/

section
variable (s₀ : State)

/-- Round key `j`, as `movdqu` loads it. -/
abbrev key (j : Nat) : BitVec 128 := s₀.mem.readW (W s₀ + BitVec.ofNat 64 (16 * j)) 128

/-- The key schedule. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1))

end

theorem key_bytes (s₀ : State) {j : Nat} (hj : j ≤ R s₀) :
    ∀ i < 16, byte (key s₀ j) i = (roundKey (sch s₀) j).getD i 0 :=
  byte_roundKey _ _ (by omega)

theorem key_in {s₀ : State} (hp : CPre s₀) {j : Nat} (hj : j ≤ 14) :
    InRegions (s₀.rd ++ s₀.wr) (W s₀ + BitVec.ofNat 64 (16 * j)) 16 := by
  rw [hp.rd]
  exact ⟨schR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩

/-- The registers of round keys 1 to 13. -/
def keyRegs : List XReg :=
  [.xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14]

theorem kreg_mem : ∀ j < 13, kreg (j + 1) ∈ keyRegs := by decide
theorem kreg_inj : ∀ i < 13, ∀ j < 13, kreg (i + 1) = kreg (j + 1) → i = j := by decide
theorem kreg_ne : ∀ j < 13, kreg (j + 1) ≠ .xmm0 ∧ kreg (j + 1) ≠ .xmm1 ∧ kreg (j + 1) ≠ .xmm15 := by
  decide

/-! ## Instructions -/

theorem xop_bin (op : XBinOp) (d r : XReg) (s : State) :
    XOp.exec (.bin op d r) s = s.setXmm d (op.eval (s.xmm d) (s.xmm r)) := rfl

theorem key_zero (s₀ : State) : key s₀ 0 = s₀.mem.readW (W s₀ + BitVec.ofNat 64 0) 128 := by
  show s₀.mem.readW (W s₀ + BitVec.ofNat 64 (16 * 0)) 128 = _
  rw [Nat.mul_zero]

theorem exec_load {b : XReg} {r : Reg} {d : Nat} {s : State}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 d) 16) :
    isa.exec (.movdquLoad b (at_ r d)) s =
      some (s.setXmm b (s.mem.readW (s.gpr r + BitVec.ofNat 64 d) 128)) := by
  show (s.load128 (s.gpr r + BitVec.ofNat 64 d)).map _ = _
  simp only [State.load128, hin, ↓reduceIte]; rfl

theorem xframe_setXmm {rs : List XReg} {s s' : State} (h : XFrame rs s s') {r : XReg} (hr : r ∈ rs)
    (v : BitVec 128) : XFrame rs s (s'.setXmm r v) :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r' hr' => by
    rw [xmm_setXmm_of_ne _ _ fun e => hr' (by rw [e]; exact hr), h.xmm r' hr']⟩

theorem loadKeys_ok {s₀ : State} (hp : CPre s₀) {s : State} (hdi : s.gpr .rdi = W s₀)
    (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    ∀ k ≤ 13, WP isa (.block (loadKeys k)) s fun s' =>
      (∀ j < k, s'.xmm (kreg (j + 1)) = key s₀ (j + 1)) ∧ XFrame keyRegs s s'
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), XFrame.refl _ _⟩
  | k + 1, hk => by
    rw [loadKeys, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (loadKeys_ok hp hdi hm hrd hwr k (by omega)) fun s₁ ⟨e₁, f₁⟩ => ?_
    rw [List.map_cons, List.map_nil, WP.block_cons_iff]
    have hin : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 (16 * (k + 1))) 16 := by
      rw [f₁.rd, f₁.wr, f₁.gpr, hrd, hwr, hdi]; exact key_in hp (by omega)
    refine ⟨_, exec_load hin, WP.block_nil ⟨fun j hj => ?_, xframe_setXmm f₁ (kreg_mem k (by omega)) _⟩⟩
    by_cases hjk : j = k
    · subst hjk
      rw [xmm_setXmm_self, f₁.mem, f₁.gpr, hm, hdi]
    · rw [xmm_setXmm_of_ne _ _ fun e => hjk (kreg_inj j (by omega) k (by omega) e), e₁ j (by omega)]

/-! ## The setup -/

/-- After the setup: the round keys in their registers, `K₀` in `xmm1`, and
the chaining value `⊕ K₀` in `xmm0`. -/
structure SInv (s₀ : State) (s : State) : Prop where
  keys : ∀ j < 13, s.xmm (kreg (j + 1)) = key s₀ (j + 1)
  k0 : s.xmm .xmm1 = key s₀ 0
  state : bytes (s.xmm .xmm0 ^^^ key s₀ 0) = Spec.Aes.bytesAt s₀.mem (St s₀) 16
  gpr : s.gpr = s₀.gpr
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem SInv.of_xframe {s₀ s s' : State} (h : SInv s₀ s) (f : XFrame [] s s') : SInv s₀ s' :=
  ⟨fun j hj => by rw [f.xmm _ (by simp)]; exact h.keys j hj, by rw [f.xmm _ (by simp)]; exact h.k0,
    by rw [f.xmm _ (by simp)]; exact h.state, f.gpr.trans h.gpr, f.mem.trans h.mem, f.rd.trans h.rd,
    f.wr.trans h.wr⟩

theorem xor_xor_cancel (a b : BitVec 128) : a ^^^ b ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- `K₀` into `xmm1`, and `C ⊕ K₀` into `xmm0`. -/
theorem start_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 0) 16)
    (hst : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 16) :
    WP isa (.block [.movdquLoad .xmm1 (at_ .rdi 0), .movdquLoad .xmm0 (at_ .rdx 0),
      .xop (.bin .pxor .xmm0 .xmm1)]) s fun s' =>
      s'.xmm .xmm1 = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 0) 128 ∧
      s'.xmm .xmm0 = s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 0) 128 ^^^
        s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 0) 128 ∧
      XFrame [.xmm0, .xmm1] s s' := by
  rw [WP.block_cons_iff]
  refine ⟨_, exec_load h0, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_load (b := .xmm0) (by rw [rd_setXmm, wr_setXmm, gpr_setXmm]; exact hst), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  simp only [XOp.exec, XBinOp.eval, xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm1 = .xmm0),
    gpr_setXmm, mem_setXmm]
  refine ⟨trivial, trivial, rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [xmm_setXmm_of_ne _ _ hr.1, xmm_setXmm_of_ne _ _ hr.1, xmm_setXmm_of_ne _ _ hr.2]

/-- The setup, from a state whose registers and memory are those of `s₀`. -/
theorem setup_ok {s₀ : State} (hp : CPre s₀) {s : State} (hg : s.gpr = s₀.gpr) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block setup) s fun s' => SInv s₀ s' ∧
      s'.zf = some (BitVec.ofNat 64 (R s₀) - (10 : BitVec 32).signExtend 64 == 0) := by
  rw [setup, WP.block_append_iff, WP.block_append_iff]
  have in0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 0) 16 := by
    rw [hrd, hwr, hg]; exact key_in hp (j := 0) (by decide)
  have inSt : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 16 := by
    rw [hrd, hwr, hg, hp.rd, hp.wr, BitVec.add_zero]
    exact ⟨stR s₀, by simp, Region.contains_self _ _⟩
  refine WP.mono (start_ok s in0 inSt) fun s₁ ⟨x1, x0, f₁⟩ => ?_
  refine WP.mono (loadKeys_ok hp (by rw [f₁.gpr, hg]) (by rw [f₁.mem, hm])
    (by rw [f₁.rd, hrd]) (by rw [f₁.wr, hwr]) 13 (Nat.le_refl _)) fun s₂ ⟨e₂, f₂⟩ => ?_
  have hrsi : s₂.gpr .rsi = BitVec.ofNat 64 (R s₀) := by
    rw [f₂.gpr, f₁.gpr, hg, rsi_ofNat]
  refine WP.mono (cmpRsi_ok s₂ 10 (R s₀) hrsi) fun s₃ ⟨z₃, f₃⟩ => ⟨SInv.of_xframe ?_ f₃, z₃⟩
  have k1 : s₂.xmm .xmm1 = key s₀ 0 := by
    rw [f₂.xmm _ (by decide), x1, hm, hg]
  refine ⟨e₂, k1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₂.xmm _ (by decide), x0, hm, hg, BitVec.add_zero]
    show bytes (_ ^^^ s₀.mem.readW (W s₀ + BitVec.ofNat 64 0) 128 ^^^
      s₀.mem.readW (W s₀ + BitVec.ofNat 64 0) 128) = _
    rw [xor_xor_cancel]
    exact bytes_read _ _
  · rw [f₂.gpr, f₁.gpr]; exact hg
  · rw [f₂.mem, f₁.mem]; exact hm
  · rw [f₂.rd, f₁.rd]; exact hrd
  · rw [f₂.wr, f₁.wr]; exact hwr

/-! ## The blocks -/

/-- After `k` blocks: the round keys in their registers, `K_Nr ⊕ K₀` in
`xmm15`, `rcx` at the next block and `r8` the number left, and `xmm0 ⊕ K₀`
the chaining value of the first `k` blocks. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  keys : ∀ j < 13, s.xmm (kreg (j + 1)) = key s₀ (j + 1)
  last : s.xmm .xmm15 = key s₀ (R s₀) ^^^ key s₀ 0
  rdi : s.gpr .rdi = W s₀
  rdx : s.gpr .rdx = St s₀
  rcx : s.gpr .rcx = Dp s₀ + BitVec.ofNat 64 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (N s₀ - k)
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : bytes (s.xmm .xmm0 ^^^ key s₀ 0) =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take k)

theorem last_ok {s₀ : State} (hp : CPre s₀) {s : State} (h : SInv s₀ s) :
    WP isa (.block (last (R s₀))) s (Inv s₀ 0) := by
  have hR : R s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  rw [last, WP.block_cons_iff]
  refine ⟨_, exec_load (by rw [h.rd, h.wr, h.gpr]; exact key_in hp hR), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [xop_bin]
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, h.mem, h.rd, h.wr, ?_⟩
  · have := kreg_ne j hj
    rw [xmm_setXmm_of_ne _ _ this.2.2, xmm_setXmm_of_ne _ _ this.2.2]; exact h.keys j hj
  · rw [xmm_setXmm_self, xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm1 = .xmm15), h.k0,
      h.mem, h.gpr]
    rfl
  · rw [gpr_setXmm, gpr_setXmm, h.gpr]
  · rw [gpr_setXmm, gpr_setXmm, h.gpr]
  · rw [gpr_setXmm, gpr_setXmm, h.gpr, Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [gpr_setXmm, gpr_setXmm, h.gpr, Nat.sub_zero]; exact r8_ofNat s₀
  · rw [xmm_setXmm_of_ne _ _ (by decide), xmm_setXmm_of_ne _ _ (by decide), List.take_zero]
    exact h.state

/-- Rounds 1 to `k` of the state in `xmm0`, with the round keys in their
registers. -/
theorem rounds_ok {s₀ : State} {x : Spec.Aes.State} {s : State}
    (hk : ∀ j < 13, s.xmm (kreg (j + 1)) = key s₀ (j + 1)) (h0 : st (s.xmm .xmm0) = rnds (sch s₀) x 0) :
    ∀ k, k < R s₀ → k ≤ 13 → WP isa (.block (rounds k)) s fun s' =>
      st (s'.xmm .xmm0) = rnds (sch s₀) x k ∧ XFrame [.xmm0] s s'
  | 0, _, _ => WP.block_nil ⟨h0, XFrame.refl _ _⟩
  | k + 1, hk₁, hk₂ => by
    rw [rounds, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (rounds_ok hk h0 k (by omega) (by omega)) fun s₁ ⟨e₁, f₁⟩ => ?_
    rw [List.map_cons, List.map_nil, WP.block_cons_iff]
    refine ⟨_, rfl, WP.block_nil ⟨?_, xframe_setXmm f₁ (List.mem_singleton_self _) _⟩⟩
    have hkey : s₁.xmm (kreg (k + 1)) = key s₀ (k + 1) := by
      rw [f₁.xmm _ (by simpa using (kreg_ne k (by omega)).1), hk k (by omega)]
    rw [XOp.exec, xmm_setXmm_self, aesenc_st _ _ (roundKey (sch s₀) (k + 1))
      (by rw [hkey]; exact key_bytes s₀ (by omega)), e₁, rnds_succ]

/-- The last round, with `K_Nr ⊕ K₀`, leaves the cipher's output `⊕ K₀`. -/
theorem last_round {nr : Nat} {w : List Byte} {x : Spec.Aes.State} {V KL K0 : BitVec 128}
    (hV : st V = rnds w x (nr - 1)) (hKL : ∀ i < 16, byte KL i = (roundKey w nr).getD i 0) :
    st (XBinOp.eval .aesenclast V (KL ^^^ K0) ^^^ K0) = cipher nr w x := by
  have e : XBinOp.eval .aesenclast V (KL ^^^ K0) ^^^ K0 = XBinOp.eval .aesenclast V KL := by
    simp only [XBinOp.eval, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rw [e, aesenclast_st _ _ _ hKL, hV, cipher_eq]

/-- On to the next block (ZF is set when none are left). -/
theorem adv_ok (s : State) :
    ∃ s', runBlock isa [.alu .add .rcx (.imm 16), .alu .sub .r8 (.imm 1)] s = some s' ∧
      s'.gpr .rcx = s.gpr .rcx + BitVec.ofNat 64 16 ∧ s'.gpr .r8 = s.gpr .r8 - 1 ∧
      s'.zf = some ((s.gpr .r8 - 1) == 0) ∧ (∀ r, r ≠ .rcx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, runBlock_cons,
      runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · exact gpr_setReg_self _ _ _
  · rw [zf_setReg, zf_arithFlags]; simp
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

theorem xor_comm3 (a k m : BitVec 128) : a ^^^ k ^^^ m ^^^ k = a ^^^ m := by
  rw [BitVec.xor_assoc, BitVec.xor_comm m k, ← BitVec.xor_assoc, xor_xor_cancel]

theorem body_ok {s₀ : State} (hp : CPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : Inv s₀ k s) :
    WP isa (.block (body (R s₀))) s fun s' =>
      Inv s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)) := by
  have hR : R s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hR₁ : 1 ≤ R s₀ := by rcases hp.rounds with h | h | h <;> omega
  have hdw := hp.data_wrap
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 0) 16 := by
    rw [h.rd, h.wr, h.rcx, BitVec.add_zero, hp.rd]
    exact ⟨dataR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hM : s.mem.readW (s.gpr .rcx + BitVec.ofNat 64 0) 128 =
      s₀.mem.readW (Dp s₀ + BitVec.ofNat 64 (16 * k)) 128 := by
    rw [h.mem, h.rcx, BitVec.add_zero]
  rw [body, WP.block_append_iff, WP.block_append_iff, WP.block_cons_iff]
  refine ⟨_, exec_load hin, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  -- The first `AddRoundKey`, of `C ⊕ M` (`x`).
  have h0 : st (s.xmm .xmm0 ^^^ s₀.mem.readW (Dp s₀ + BitVec.ofNat 64 (16 * k)) 128) =
      rnds (sch s₀) (st (s.xmm .xmm0 ^^^ key s₀ 0 ^^^ s₀.mem.readW (Dp s₀ + BitVec.ofNat 64 (16 * k)) 128))
        0 := by
    rw [rnds_zero, ← pxor_st _ _ _ (key_bytes s₀ (j := 0) (by omega)), XBinOp.eval, xor_comm3]
  refine WP.mono (rounds_ok (s₀ := s₀)
      (x := st (s.xmm .xmm0 ^^^ key s₀ 0 ^^^ s₀.mem.readW (Dp s₀ + BitVec.ofNat 64 (16 * k)) 128))
      (fun j hj => ?_) ?_ (R s₀ - 1) (by omega) (by omega))
    fun s₂ ⟨e₂, f₂⟩ => ?_
  · have := kreg_ne j hj
    simp only [XOp.exec, xmm_setXmm_of_ne _ _ this.1, xmm_setXmm_of_ne _ _ this.2.1]
    exact h.keys j hj
  · simp only [XOp.exec, XBinOp.eval, xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm0 = .xmm1),
      hM]
    exact h0
  -- The last round and the advance.
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  obtain ⟨s₃, run₃, rcx₃, r8₃, zf₃, keep₃, mem₃, rd₃, wr₃, xmm₃⟩ := adv_ok
    (XOp.exec (.bin .aesenclast .xmm0 .xmm15) s₂)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  -- What the block left unchanged.
  have hx : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → s₃.xmm r = s.xmm r := fun r h₀ h₁ => by
    rw [xmm₃, XOp.exec, xmm_setXmm_of_ne _ _ h₀, f₂.xmm _ (by simpa using h₀)]
    simp only [XOp.exec, xmm_setXmm_of_ne _ _ h₀, xmm_setXmm_of_ne _ _ h₁]
  have hg : ∀ r, r ≠ .rcx → r ≠ .r8 → s₃.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [keep₃ r h₁ h₂, XOp.exec, gpr_setXmm, f₂.gpr]; rfl
  have g8 : (XOp.exec (.bin .aesenclast .xmm0 .xmm15) s₂).gpr .r8 = s.gpr .r8 := by
    rw [XOp.exec, gpr_setXmm, f₂.gpr]; rfl
  have gc : (XOp.exec (.bin .aesenclast .xmm0 .xmm15) s₂).gpr .rcx = s.gpr .rcx := by
    rw [XOp.exec, gpr_setXmm, f₂.gpr]; rfl
  have hN := (s₀.gpr .r8).isLt
  have dec : BitVec.ofNat 64 (N s₀ - k) - 1 = BitVec.ofNat 64 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  refine ⟨⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have := kreg_ne j hj
    rw [hx _ this.1 this.2.1]; exact h.keys j hj
  · rw [hx _ (by decide) (by decide)]; exact h.last
  · rw [hg _ (by decide) (by decide)]; exact h.rdi
  · rw [hg _ (by decide) (by decide)]; exact h.rdx
  · rw [rcx₃, gc, h.rcx, Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega)]
  · rw [r8₃, g8, h.r8, dec]
  · rw [mem₃, XOp.exec, mem_setXmm, f₂.mem]; exact h.mem
  · rw [rd₃, XOp.exec, rd_setXmm, f₂.rd]; exact h.rd
  · rw [wr₃, XOp.exec, wr_setXmm, f₂.wr]; exact h.wr
  · -- `CIPH_K(C ⊕ M) ⊕ K₀`.
    have hL : s₂.xmm .xmm15 = key s₀ (R s₀) ^^^ key s₀ 0 := by
      rw [f₂.xmm _ (by decide)]
      simp only [XOp.exec, xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm15 = .xmm0),
        xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm15 = .xmm1)]
      exact h.last
    have hc : st ((s₃.xmm .xmm0) ^^^ key s₀ 0) = cipher (R s₀) (sch s₀)
        (st (s.xmm .xmm0 ^^^ key s₀ 0 ^^^ s₀.mem.readW (Dp s₀ + BitVec.ofNat 64 (16 * k)) 128)) := by
      rw [xmm₃, XOp.exec, xmm_setXmm_self, hL]
      exact last_round e₂ (key_bytes s₀ (Nat.le_refl _))
    rw [take_succ_blks s₀ hk, Proof.Cmac.chain_append, ← h.state, Proof.Cmac.chain_single, ← bytes_read,
      ← bytes_xor]
    exact (aesWith_bytes _ _ _ _ hc).symm
  · rw [zf₃, g8, h.r8, dec]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simpa using this
    · intro he; rw [he]; rfl

theorem loop_ok {s₀ : State} (hp : CPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : Inv s₀ k s) :
    WP isa (.loop (.block (body (R s₀))) .ne) s (Inv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ Inv s₀ j t)
    ?_ (N s₀ - k) s ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' ⟨h', zf'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by simp [eval, zf', hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    exact ⟨by simp [eval, zf', hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

theorem blocks_ok {s₀ : State} (hp : CPre s₀) (hn : 0 < N s₀) {s : State} (h : SInv s₀ s) :
    WP isa (blocks (R s₀)) s (Inv s₀ (N s₀)) :=
  WP.seq (WP.mono (last_ok hp h) fun _ h₁ => loop_ok hp hn h₁)

theorem cmp_eval {s : State} {n : Nat} (c : Nat) (hn : n = 10 ∨ n = 12 ∨ n = 14) (hc : c = 10 ∨ c = 12)
    (hz : s.zf = some (BitVec.ofNat 64 n - (BitVec.ofNat 32 c).signExtend 64 == 0)) :
    isa.eval .e s = some (decide (n = c)) := by
  show s.zf = _
  rw [hz]
  rcases hn with rfl | rfl | rfl <;> rcases hc with rfl | rfl <;> decide

theorem loops_ok {s₀ : State} (hp : CPre s₀) (hn : 0 < N s₀) {s : State} (h : SInv s₀ s)
    (hz : s.zf = some (BitVec.ofNat 64 (R s₀) - (10 : BitVec 32).signExtend 64 == 0)) :
    WP isa loops s (Inv s₀ (N s₀)) := by
  have hrsi : s.gpr .rsi = BitVec.ofNat 64 (R s₀) := by rw [h.gpr, rsi_ofNat]
  refine WP.ite (decide (R s₀ = 10)) (cmp_eval 10 hp.rounds (by decide) hz) (fun h10 => ?_) fun h10 => ?_
  · have hb := blocks_ok hp hn h
    rwa [of_decide_eq_true h10] at hb
  · refine WP.seq (WP.mono (cmpRsi_ok s 12 (R s₀) hrsi) fun s₁ ⟨z₁, f₁⟩ => ?_)
    have hb := blocks_ok hp hn (h.of_xframe f₁)
    refine WP.ite (decide (R s₀ = 12)) (cmp_eval 12 hp.rounds (by decide) z₁) (fun h12 => ?_) fun h12 => ?_
    · rwa [of_decide_eq_true h12] at hb
    · have h14 : R s₀ = 14 := by
        have := of_decide_eq_false h10
        have := of_decide_eq_false h12
        rcases hp.rounds with e | e | e <;> omega
      rwa [h14] at hb

/-! ## The whole function -/

theorem exec_store {b : XReg} {r : Reg} {d : Nat} {s : State}
    (hin : InRegions s.wr (s.gpr r + BitVec.ofNat 64 d) 16) :
    isa.exec (.movdquStore (at_ r d) b) s =
      some { s with mem := s.mem.writeW (s.gpr r + BitVec.ofNat 64 d) (s.xmm b) } := by
  show s.store128 (s.gpr r + BitVec.ofNat 64 d) (s.xmm b) = _
  simp only [State.store128, hin, ↓reduceIte]

theorem finish_wp (s : State) (h₁ : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 0) 16)
    (h₂ : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 0) 16) :
    WP isa (.block finish) s fun s' => s'.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofNat 64 0)
      (s.xmm .xmm0 ^^^ s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 0) 128) := by
  rw [finish, WP.block_cons_iff]
  refine ⟨_, exec_load h₁, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff, xop_bin]
  refine ⟨_, exec_store h₂, WP.block_nil ?_⟩
  show (s.mem.writeW _ _ : Mem) = _
  rw [xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm0 = .xmm1), xmm_setXmm_self]
  rfl

theorem finish_ok {s₀ : State} (hp : CPre s₀) {s : State} (h : Inv s₀ (N s₀) s) :
    WP isa (.block finish) s fun s' =>
      Spec.Aes.bytesAt s'.mem (St s₀) 16 =
        Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (St s₀) 16) (blks s₀) ∧
      Frame [stR s₀] s₀.mem s'.mem := by
  refine WP.mono (finish_wp s (by rw [h.rd, h.wr, h.rdi]; exact key_in hp (j := 0) (by decide)) (by
    rw [h.wr, h.rdx, hp.wr, BitVec.add_zero]
    exact ⟨stR s₀, by simp, Region.contains_self _ _⟩)) fun s' hm => ?_
  rw [hm, h.mem, h.rdx, h.rdi, BitVec.add_zero, ← key_zero]
  refine ⟨?_, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩
  rw [bytes_write, h.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem correct_wp {s₀ : State} (hp : CPre s₀) :
    WP isa update s₀ fun s' =>
      Spec.Aes.bytesAt s'.mem (St s₀) 16 =
        Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (St s₀) 16) (blks s₀) ∧
      Frame [stR s₀] s₀.mem s'.mem := by
  have hN := (s₀.gpr .r8).isLt
  rw [update]
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  have ev : isa.eval .e (arithFlags s₀ (s₀.gpr .r8 &&& s₀.gpr .r8) false false) =
      some (decide (N s₀ = 0)) := by
    show (arithFlags s₀ _ false false).zf = _
    rw [zf_arithFlags, BitVec.and_self, r8_ofNat, beq_zero hN]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ⟨?_, Frame.refl _ _⟩)
      (fun h => by cases h)
    simp [Spec.Cmac.blocksAt, hn, Spec.Cmac.chain, mem_arithFlags]
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    refine WP.seq (WP.mono (setup_ok hp rfl rfl rfl rfl) fun s₁ ⟨h₁, z₁⟩ => ?_)
    exact WP.seq (WP.mono (loops_ok hp (by omega) h₁ z₁) fun s₂ h₂ => finish_ok hp h₂)

/-- No instruction writes a callee-saved register. -/
theorem keeps (r : Reg) (hr : r ∈ calleeSaved) : ∀ i ∈ instrs update, Taint.clobbers i r = false := by
  have h : update.allInstrs (fun i => calleeSaved.all fun r => !Taint.clobbers i r) = true := by
    decide +kernel
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  intro i hi
  simpa using List.all_eq_true.mp (h i hi) r hr

theorem correct (s : State) (hs : cbcX86_64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ cbcX86_64.post s s' := by
  have hp := CPre.of hs
  obtain ⟨t, s', he, hq, hf⟩ := correct_wp hp
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he
    ⟨fun r hr => Exec.gpr (keeps r hr) he, ?_⟩, hq⟩
  exact hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.ret_st) (by decide)

theorem ct : ConstantTime isa cbcX86_64.pre cbcX86_64.pub update := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, h7⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (with no blocks). -/
def cbcSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem verified : Verified X86_64.target update (Spec.Cmac.aesUpdateContract X86_64.abi) :=
  Verified.of_correct correct ct (by
    sig_implies [Spec.Cmac.aesUpdateContract, Spec.Cmac.aesUpdateSig, cbcX86_64, X86_64.abi,
      X86_64.argRegs] [cbcSat] using cbcSat)

/-! ## As an implementation of `vg_cmac_aes_update` for its callers -/

theorem update_ok (s : State) (hs : updateX86_64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updateX86_64.post s s' :=
  correct s (pre_of_update hs)

theorem update_ct : ConstantTime isa updateX86_64.pre updateX86_64.pub update :=
  fun _ _ _ _ _ _ h₁ h₂ hq => ct _ _ _ _ _ _ (pre_of_update h₁) (pre_of_update h₂) hq

end VG.Proof.CmacAes.X86_64.AesNi

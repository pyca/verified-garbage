module

public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Impl.AesCbc.X86_64.Decrypt
public import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
public import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
import VerifiedGarbage.Proof.AesCbc.Decrypt
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Impl.AesCbc.X86_64.Decrypt
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.AesCbc.X86_64.Encrypt
import VerifiedGarbage.Proof.AesCbc.Mem
public import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
public import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.CmacAes.X86_64.AesNi
meta import VerifiedGarbage.Impl.AesCbc.X86_64.Encrypt
meta import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
meta import VerifiedGarbage.Spec.Cmac.Contract
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `AesCbc.X86_64.Encrypt`, which this module and modules that import it used -/

section

/-!
# CBC encryption with AES-NI, the round keys read from the schedule

The chaining register holds the last ciphertext block between blocks. Each
round loads its key from the schedule, which the data written so far is
apart from. The invariant records the processed ciphertext prefix, the
untouched plaintext suffix, and a frame containing only the data. All three
key sizes select a specialized loop before processing the message. The code
has no frame and no call, and its contract (`encContract`) asks nothing of
the stack below the return address.
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86_64.Encrypt

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.CmacAes.X86_64 (W R St Dp N S schR stR dataR scrR ciph blks rsi_ofNat r8_ofNat beq_zero take_succ_blks)
open VG.Proof.Aes.X86_64.AesNi (st st_ext getD_st byte_xor pxor_st aesenc_st aesenclast_st rnds
  rnds_zero rnds_succ cipher_eq byte_roundKey XFrame cmpRsi_ok)
open VG.Impl.CmacAes.X86_64.AesNi (at_)
open VG.Impl.AesCbc.X86_64.Encrypt
open VG.Spec.Aes (roundKey cipher)

/-! ## The contract -/

/-- `vg_aes_cbc_encrypt`'s contract (`cbcX86_64 true`), for code that uses
no stack and no `scratch`: nothing is asked of the stack below the return
address. -/
def encContract : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let iv : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2176⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint data ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧ data.Disjoint scr ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧
      (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post := (VG.Proof.AesCbc.X86_64.cbcX86_64 true).post
  pub := (VG.Proof.AesCbc.X86_64.cbcX86_64 true).pub

/-- The precondition, by name. -/
structure CPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀]
  wr : s₀.wr = [stR s₀, dataR s₀, scrR s₀]
  sch_data : (schR s₀).Disjoint (dataR s₀)
  iv_data : (stR s₀).Disjoint (dataR s₀)
  iv_scr : (stR s₀).Disjoint (scrR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  ret_iv : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (stR s₀)
  ret_data : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (dataR s₀)
  data_wrap : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem CPre.of {s₀ : State} (h : encContract.pre s₀) : CPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j⟩

abbrev encChain (s₀ : State) (iv : List Byte) (xs : List (List Byte)) : List Byte :=
  Spec.Cbc.next iv (Spec.Cbc.encrypt (VG.Proof.CmacAes.X86_64.ciph s₀) iv xs)

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
  byte_roundKey _ _ (by omega_arith)

theorem key_in {s₀ : State} (hp : CPre s₀) {j : Nat} (hj : j ≤ 14) :
    InRegions (s₀.rd ++ s₀.wr) (W s₀ + BitVec.ofNat 64 (16 * j)) 16 := by
  rw [hp.rd]
  exact ⟨schR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- A round key is apart from the data, the only memory written before the
chaining value is stored. -/
theorem key_unchanged {s₀ s : State} (hp : CPre s₀) (hf : Frame [dataR s₀] s₀.mem s.mem) {j : Nat}
    (hj : j ≤ 14) : s.mem.readW (W s₀ + BitVec.ofNat 64 (16 * j)) 128 = key s₀ j :=
  hf.readW (r := ⟨W s₀ + BitVec.ofNat 64 (16 * j), 16⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.sch_data.sub_left (Offset.sub_base _ (by omega_arith))) (by decide)

/-! ## Instructions -/


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


theorem exec_store {b : XReg} {r : Reg} {d : Nat} {s : State}
    (hin : InRegions s.wr (s.gpr r + BitVec.ofNat 64 d) 16) :
    isa.exec (.movdquStore (at_ r d) b) s =
      some { s with mem := s.mem.writeW (s.gpr r + BitVec.ofNat 64 d) (s.xmm b) } := by
  show s.store128 (s.gpr r + BitVec.ofNat 64 d) (s.xmm b) = _
  simp only [State.store128, hin, ↓reduceIte]

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

/-! ## The blocks -/

/-- After `k` blocks: `rcx` at the next block and `r8` the number left,
`xmm0` the chaining value of the first `k` blocks, which are encrypted in
place, the rest as they were. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = W s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  rdx : s.gpr .rdx = St s₀
  rcx : s.gpr .rcx = Dp s₀ + BitVec.ofNat 64 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (N s₀ - k)
  frame : Frame [dataR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : bytes (s.xmm .xmm0) = encChain s₀ (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take k)
  data : Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) =
    Spec.Cbc.encrypt (VG.Proof.CmacAes.X86_64.ciph s₀) (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take k) ++ (blks s₀).drop k

theorem Inv.of_xframe {s₀ : State} {k : Nat} {s s' : State} (h : Inv s₀ k s) (f : XFrame [] s s') :
    Inv s₀ k s' :=
  ⟨by rw [f.gpr]; exact h.rdi, by rw [f.gpr]; exact h.rsi, by rw [f.gpr]; exact h.rdx, by rw [f.gpr]; exact h.rcx,
    by rw [f.gpr]; exact h.r8, by rw [f.mem]; exact h.frame, f.rd.trans h.rd, f.wr.trans h.wr,
    by rw [f.xmm _ (by simp)]; exact h.state, by rw [f.mem]; exact h.data⟩

/-- Rounds 1 to `k` of the state in `xmm0`, each with its key from the
schedule. -/
theorem rounds_ok {s₀ : State} (hp : CPre s₀) {x : Spec.Aes.State} {s : State}
    (hdi : s.gpr .rdi = W s₀) (hf : Frame [dataR s₀] s₀.mem s.mem) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (h0 : st (s.xmm .xmm0) = rnds (sch s₀) x 0) :
    ∀ k, k < R s₀ → WP isa (.block (rounds k)) s fun s' =>
      st (s'.xmm .xmm0) = rnds (sch s₀) x k ∧ XFrame [.xmm0, .xmm1] s s'
  | 0, _ => WP.block_nil ⟨h0, XFrame.refl _ _⟩
  | k + 1, hk => by
    have hR : R s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
    rw [rounds, List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (rounds_ok hp hdi hf hrd hwr h0 k (by omega_arith)) fun s₁ ⟨e₁, f₁⟩ => ?_
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, round, WP.block_cons_iff]
    refine ⟨_, exec_load (by rw [f₁.rd, f₁.wr, f₁.gpr, hrd, hwr, hdi]; exact key_in hp (by omega_arith)), ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨_, rfl, WP.block_nil ⟨?_, xframe_setXmm (xframe_setXmm f₁ (by simp) _) (by simp) _⟩⟩
    have hkey : s₁.mem.readW (s₁.gpr .rdi + BitVec.ofNat 64 (16 * (k + 1))) 128 = key s₀ (k + 1) := by
      rw [f₁.mem, f₁.gpr, hdi]; exact key_unchanged hp hf (by omega_arith)
    rw [xop_bin, xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm0 = .xmm1), xmm_setXmm_self,
      aesenc_st _ _ (roundKey (sch s₀) (k + 1)) (by rw [hkey]; exact key_bytes s₀ (by omega_arith)), e₁,
      rnds_succ]

/-- `xmm0 ⊕ (M ⊕ K₀)`, for the block `M` at `rcx`. -/
theorem first_ok (s : State) (hm : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 0) 16)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 0) 16) :
    WP isa (.block first) s fun s' =>
      s'.xmm .xmm0 = s.xmm .xmm0 ^^^ (s.mem.readW (s.gpr .rcx + BitVec.ofNat 64 0) 128 ^^^
        s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 0) 128) ∧
      XFrame [.xmm0, .xmm1, .xmm2] s s' := by
  rw [first, WP.block_cons_iff]
  refine ⟨_, exec_load hm, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_load (b := .xmm2) (by rw [rd_setXmm, wr_setXmm, gpr_setXmm]; exact h0), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  simp only [XOp.exec, XBinOp.eval, xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm0 = .xmm1),
    xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm0 = .xmm2), xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm1 = .xmm2),
    gpr_setXmm, mem_setXmm]
  refine ⟨trivial, rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [xmm_setXmm_of_ne _ _ hr.1, xmm_setXmm_of_ne _ _ hr.2.1, xmm_setXmm_of_ne _ _ hr.2.2,
    xmm_setXmm_of_ne _ _ hr.2.1]

/-- The last round with its key from the schedule, and the block stored at
`rcx`. -/
theorem last_ok (nr : Nat) (s : State)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) 16)
    (hout : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 0) 16) :
    WP isa (.block [.movdquLoad .xmm1 (at_ .rdi (16 * nr)), .xop (.bin .aesenclast .xmm0 .xmm1),
      .movdquStore (at_ .rcx 0) .xmm0]) s fun t =>
      t.xmm .xmm0 = XBinOp.eval .aesenclast (s.xmm .xmm0)
        (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) 128) ∧
      t.mem = s.mem.writeW (s.gpr .rcx + BitVec.ofNat 64 0) (t.xmm .xmm0) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [WP.block_cons_iff]
  refine ⟨_, exec_load hk, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff, xop_bin]
  refine ⟨_, exec_store (by rw [wr_setXmm, wr_setXmm, gpr_setXmm, gpr_setXmm]; exact hout), WP.block_nil ?_⟩
  simp only [xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide : ¬XReg.xmm0 = .xmm1), gpr_setXmm, mem_setXmm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

/-- The last round, the block stored, and the advance. -/
theorem final_ok (nr : Nat) (s : State)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) 16)
    (hout : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 0) 16) :
    WP isa (.block (final nr)) s fun t =>
      t.xmm .xmm0 = XBinOp.eval .aesenclast (s.xmm .xmm0)
        (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) 128) ∧
      t.mem = s.mem.writeW (s.gpr .rcx + BitVec.ofNat 64 0) (t.xmm .xmm0) ∧
      t.gpr .rcx = s.gpr .rcx + BitVec.ofNat 64 16 ∧ t.gpr .r8 = s.gpr .r8 - 1 ∧
      t.zf = some ((s.gpr .r8 - 1) == 0) ∧ (∀ r, r ≠ .rcx → r ≠ .r8 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  rw [final, show ([.movdquLoad .xmm1 (at_ .rdi (16 * nr)), .xop (.bin .aesenclast .xmm0 .xmm1),
      .movdquStore (at_ .rcx 0) .xmm0, .alu .add .rcx (.imm 16), .alu .sub .r8 (.imm 1)] : List Instr) =
    [.movdquLoad .xmm1 (at_ .rdi (16 * nr)), .xop (.bin .aesenclast .xmm0 .xmm1),
      .movdquStore (at_ .rcx 0) .xmm0] ++ [.alu .add .rcx (.imm 16), .alu .sub .r8 (.imm 1)] from rfl,
    WP.block_append_iff]
  refine WP.mono (last_ok nr s hk hout) fun u ⟨xu, mu, gu, ru, wu⟩ => ?_
  obtain ⟨s₃, run₃, rcx₃, r8₃, zf₃, keep₃, mem₃, rd₃, wr₃, xmm₃⟩ := adv_ok u
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨by rw [xmm₃, xu], by rw [mem₃, xmm₃, mu], by rw [rcx₃, gu], by rw [r8₃, gu], by rw [zf₃, gu],
    fun r h₁ h₂ => by rw [keep₃ r h₁ h₂, gu], rd₃.trans ru, wr₃.trans wu⟩

theorem body_ok {s₀ : State} (hp : CPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : Inv s₀ k s) :
    WP isa (.block (body (R s₀))) s fun t =>
      Inv s₀ (k + 1) t ∧ t.zf = some (decide (N s₀ - (k + 1) = 0)) := by
  have hR : R s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  have hR₁ : 1 ≤ R s₀ := by rcases hp.rounds with h | h | h <;> omega_arith
  have hdw := hp.data_wrap
  have hN := (s₀.gpr .r8).isLt
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 0) 16 := by
    rw [h.rd, h.wr, h.rcx, BitVec.add_zero, hp.rd, hp.wr]
    exact ⟨dataR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hout : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 0) 16 := by
    rw [h.wr, h.rcx, BitVec.add_zero, hp.wr]
    exact ⟨dataR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hM : s.mem.readW (s.gpr .rcx + BitVec.ofNat 64 0) 128 =
      s₀.mem.readW (Dp s₀ + BitVec.ofNat 64 (16 * k)) 128 := by
    rw [h.rcx, BitVec.add_zero]
    apply VG.Proof.Aes.X86_64.AesNi.st_inj
    rw [← VG.Proof.Aes.X86_64.AesNi.stateAt_eq, ← VG.Proof.Aes.X86_64.AesNi.stateAt_eq]
    apply Vector.toList_inj.mp
    rw [← VG.Proof.AesCbc.bytesAt_toList, ← VG.Proof.AesCbc.bytesAt_toList]
    have hd := congrArg (·[k]?) h.data
    have hl : (Spec.Cbc.encrypt (VG.Proof.CmacAes.X86_64.ciph s₀) (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take k)).length = k := by
      rw [VG.Proof.AesCbc.length_encrypt]; simp [Spec.Cbc.blocksAt]; omega_arith
    simp only [List.getElem?_eq_getElem (show k < (Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀)).length by
        rw [length_blocksAt]; exact hk),
      List.getElem?_append_right (show _ ≤ k from Nat.le_of_eq hl), hl, Nat.sub_self,
      List.getElem?_drop, Nat.add_zero,
      List.getElem?_eq_getElem (show k < (blks s₀).length by simp [Spec.Cbc.blocksAt]; exact hk)] at hd
    rw [← getElem_blocksAt _ _ hk, ← getElem_blocksAt _ _ hk]
    exact Option.some.inj hd
  have hK0 : s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 0) 128 = key s₀ 0 := by
    rw [h.rdi]; exact key_unchanged hp h.frame (j := 0) (by decide)
  rw [body, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (first_ok s hin (by
    rw [h.rd, h.wr, h.rdi]; exact key_in hp (j := 0) (by decide))) fun s₁ ⟨x₁, f₁⟩ => ?_
  -- The first `AddRoundKey`, of `C ⊕ M` (`x`).
  have h0 : st (s₁.xmm .xmm0) =
      rnds (sch s₀) (st (s.xmm .xmm0 ^^^ s₀.mem.readW (Dp s₀ + BitVec.ofNat 64 (16 * k)) 128)) 0 := by
    rw [x₁, hM, hK0, rnds_zero, ← pxor_st _ _ _ (key_bytes s₀ (j := 0) (by omega_arith)), XBinOp.eval,
      BitVec.xor_assoc]
  refine WP.mono (rounds_ok hp (by rw [f₁.gpr]; exact h.rdi) (by rw [f₁.mem]; exact h.frame)
    (f₁.rd.trans h.rd) (f₁.wr.trans h.wr) h0 (R s₀ - 1) (by omega_arith)) fun s₂ ⟨e₂, f₂⟩ => ?_
  refine WP.mono (final_ok (R s₀) s₂ (by
      rw [f₂.rd, f₂.wr, f₂.gpr, f₁.rd, f₁.wr, f₁.gpr, h.rd, h.wr, h.rdi]; exact key_in hp hR) (by
      rw [f₂.wr, f₂.gpr, f₁.wr, f₁.gpr]; exact hout))
    fun t ⟨xt, mt, rcxt, r8t, zt, gt, rdt, wrt⟩ => ?_
  have g₂ : s₂.gpr = s.gpr := f₂.gpr.trans f₁.gpr
  have m₂ : s₂.mem = s.mem := f₂.mem.trans f₁.mem
  have dec : BitVec.ofNat 64 (N s₀ - k) - 1 = BitVec.ofNat 64 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith)]; rfl
  -- `CIPH_K(C ⊕ M)`.
  have hc : st (t.xmm .xmm0) = cipher (R s₀) (sch s₀)
      (st (s.xmm .xmm0 ^^^ s₀.mem.readW (Dp s₀ + BitVec.ofNat 64 (16 * k)) 128)) := by
    rw [xt, aesenclast_st _ _ (roundKey (sch s₀) (R s₀)) (by
      rw [g₂, m₂, h.rdi, key_unchanged hp h.frame hR]; exact key_bytes s₀ (Nat.le_refl _)), e₂, cipher_eq]
  have hstate : bytes (t.xmm .xmm0) =
      encChain s₀ (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take (k + 1)) := by
    rw [take_succ_blks s₀ hk, encChain, VG.Proof.AesCbc.encrypt_snoc, VG.Proof.AesCbc.next_snoc]
    change _ = VG.Proof.CmacAes.X86_64.ciph s₀ (Spec.Cmac.xor _ _)
    have xorComm (a b : List Byte) : Spec.Cmac.xor a b = Spec.Cmac.xor b a := by
      rw [Spec.Cmac.xor, List.zipWith_comm]
      simp only [BitVec.xor_comm]; rfl
    rw [xorComm]
    change _ = VG.Proof.CmacAes.X86_64.ciph s₀
      (Spec.Cmac.xor (encChain s₀ (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take k)) _)
    rw [← h.state, getElem_blocksAt _ _ hk, ← bytes_read, ← bytes_xor]
    exact (aesWith_bytes _ _ _ _ hc).symm
  have addr : s₂.gpr .rcx + BitVec.ofNat 64 0 = VG.Proof.AesCbc.X86_64.blk s₀ k := by
    rw [g₂, h.rcx, BitVec.add_zero]
  rw [addr, m₂] at mt
  have fs : Frame [⟨VG.Proof.AesCbc.X86_64.blk s₀ k, 16⟩] s.mem t.mem := by
    rw [mt]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fd : Frame [dataR s₀] s.mem t.mem := fs.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, VG.Proof.AesCbc.X86_64.UPre.data_sub hk⟩
  have newbytes : Spec.Aes.bytesAt t.mem (VG.Proof.AesCbc.X86_64.blk s₀ k) 16 =
      encChain s₀ (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take (k+1)) := by
    rw [mt, bytes_write, hstate]
  have outSucc : Spec.Cbc.encrypt (VG.Proof.CmacAes.X86_64.ciph s₀)
      (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take (k+1)) =
      Spec.Cbc.encrypt (VG.Proof.CmacAes.X86_64.ciph s₀)
      (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take k) ++
      [Spec.Aes.bytesAt t.mem (VG.Proof.AesCbc.X86_64.blk s₀ k) 16] := by
    rw [newbytes, encChain, take_succ_blks s₀ hk, VG.Proof.AesCbc.encrypt_snoc, VG.Proof.AesCbc.next_snoc]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, h.frame.trans fd, ?_, ?_, hstate, ?_⟩, ?_⟩
  · rw [gt _ (by decide) (by decide), g₂]; exact h.rdi
  · rw [gt _ (by decide) (by decide), g₂]; exact h.rsi
  · rw [gt _ (by decide) (by decide), g₂]; exact h.rdx
  · rw [rcxt, g₂, h.rcx, Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega_arith)]
  · rw [r8t, g₂, h.r8, dec]
  · rw [rdt, f₂.rd, f₁.rd]; exact h.rd
  · rw [wrt, f₂.wr, f₁.wr]; exact h.wr
  · have hs := VG.Proof.AesCbc.blocksAt_set (m := s.mem) (m' := t.mem) (p := Dp s₀) (n := N s₀) (k := k)
      (fun j hj hjk => VG.Proof.AesCbc.X86_64.bytesAt_frame fs (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using [hjk]) (by omega_using [hj, hdw]) (by omega_using [hk, hdw]))
        (by decide))
    rw [hs, h.data, outSucc, VG.Proof.AesCbc.set_prefix]
    · rw [VG.Proof.AesCbc.length_encrypt]; simp [Spec.Cbc.blocksAt]; omega_arith
    · simpa [Spec.Cbc.blocksAt] using hk
  · rw [zt, g₂, h.r8, dec]
    refine congrArg some ?_
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
      simpa using this
    · intro he; rw [he]; rfl

theorem loop_ok {s₀ : State} (hp : CPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : Inv s₀ k s) :
    WP isa (blocks (R s₀)) s (Inv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ Inv s₀ j t)
    ?_ (N s₀ - k) s ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' ⟨h', zf'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by simp [eval, zf', hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_arith]
  · right
    exact ⟨by simp [eval, zf', hz], N s₀ - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, h'⟩

theorem cmp_eval {s : State} {n : Nat} (c : Nat) (hn : n = 10 ∨ n = 12 ∨ n = 14) (hc : c = 10 ∨ c = 12)
    (hz : s.zf = some (BitVec.ofNat 64 n - (BitVec.ofNat 32 c).signExtend 64 == 0)) :
    isa.eval .e s = some (decide (n = c)) := by
  show s.zf = _
  rw [hz]
  rcases hn with rfl | rfl | rfl <;> rcases hc with rfl | rfl <;> decide

theorem loops_ok {s₀ : State} (hp : CPre s₀) (hn : 0 < N s₀) {s : State} (h : Inv s₀ 0 s)
    (hz : s.zf = some (BitVec.ofNat 64 (R s₀) - (10 : BitVec 32).signExtend 64 == 0)) :
    WP isa loops s (Inv s₀ (N s₀)) := by
  have hrsi : s.gpr .rsi = BitVec.ofNat 64 (R s₀) := by rw [h.rsi, rsi_ofNat]
  refine WP.ite (decide (R s₀ = 10)) (cmp_eval 10 hp.rounds (by decide) hz) (fun h10 => ?_) fun h10 => ?_
  · have hb := loop_ok hp hn h
    rwa [of_decide_eq_true h10] at hb
  · refine WP.seq (WP.mono (cmpRsi_ok s 12 (R s₀) hrsi) fun s₁ ⟨z₁, f₁⟩ => ?_)
    have hb := loop_ok hp hn (h.of_xframe f₁)
    refine WP.ite (decide (R s₀ = 12)) (cmp_eval 12 hp.rounds (by decide) z₁) (fun h12 => ?_) fun h12 => ?_
    · rwa [of_decide_eq_true h12] at hb
    · have h14 : R s₀ = 14 := by
        have := of_decide_eq_false h10
        have := of_decide_eq_false h12
        rcases hp.rounds with e | e | e <;> omega_arith
      rwa [h14] at hb

/-! ## The whole function -/

/-- The chaining value into `xmm0`, and `cmp rsi, 10`. -/
theorem setup_ok {s₀ : State} (hp : CPre s₀) {s : State} (hg : s.gpr = s₀.gpr) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block setup) s fun s' => Inv s₀ 0 s' ∧
      s'.zf = some (BitVec.ofNat 64 (R s₀) - (10 : BitVec 32).signExtend 64 == 0) := by
  rw [setup, WP.block_cons_iff]
  refine ⟨_, exec_load (by
    rw [hrd, hwr, hg, hp.rd, hp.wr, BitVec.add_zero]
    exact ⟨stR s₀, by simp, Region.contains_self _ _⟩), ?_⟩
  refine WP.mono (cmpRsi_ok _ 10 (R s₀) (by rw [gpr_setXmm, hg, rsi_ofNat])) fun s₁ ⟨z₁, f₁⟩ =>
    ⟨Inv.of_xframe ?_ f₁, z₁⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gpr_setXmm, hg]
  · rw [gpr_setXmm, hg]
  · rw [gpr_setXmm, hg]
  · rw [gpr_setXmm, hg, Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [gpr_setXmm, hg, Nat.sub_zero]; exact r8_ofNat s₀
  · rw [mem_setXmm, hm]; exact Frame.refl _ _
  · rw [rd_setXmm]; exact hrd
  · rw [wr_setXmm]; exact hwr
  · rw [xmm_setXmm_self, hm, hg, BitVec.add_zero, List.take_zero]
    exact bytes_read _ _
  · rw [mem_setXmm, hm]; simp [Spec.Cbc.encrypt]

theorem finish_ok {s₀ : State} (hp : CPre s₀) {s : State} (h : Inv s₀ (N s₀) s) :
    WP isa (.block finish) s fun t =>
      (encContract.post s₀ t) ∧ Frame [stR s₀, dataR s₀] s₀.mem t.mem := by
  rw [finish, WP.block_cons_iff]
  refine ⟨_, exec_store (by
    rw [h.wr, h.rdx, hp.wr, BitVec.add_zero]
    exact ⟨stR s₀, by simp, Region.contains_self _ _⟩), WP.block_nil ?_⟩
  have hm : ({ s with mem := s.mem.writeW (s.gpr .rdx + BitVec.ofNat 64 0) (s.xmm .xmm0) } : State).mem =
      s.mem.writeW (St s₀) (s.xmm .xmm0) := by
    show s.mem.writeW _ _ = _
    rw [h.rdx, BitVec.add_zero]
  generalize ({ s with mem := s.mem.writeW (s.gpr .rdx + BitVec.ofNat 64 0) (s.xmm .xmm0) } : State) = t at hm
  have ff : Frame [stR s₀] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨⟨?_, ?_⟩, (h.frame.mono (by simp)).trans (ff.mono (by simp))⟩
  · change Spec.Cbc.blocksAt t.mem (Dp s₀) (N s₀) = _
    have be : Spec.Cbc.blocksAt t.mem (Dp s₀) (N s₀) = Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) := by
      apply List.map_congr_left
      intro j hj
      exact VG.Proof.AesCbc.X86_64.bytesAt_frame ff (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.iv_data.symm.sub_left (VG.Proof.AesCbc.X86_64.UPre.data_sub (List.mem_range.mp hj))) (by decide)
    rw [be, h.data]
    have hl : (blks s₀).length ≤ N s₀ := by simp [Spec.Cbc.blocksAt]
    rw [List.take_of_length_le hl, List.drop_eq_nil_of_le hl, List.append_nil]
    rfl
  · change Spec.Aes.bytesAt t.mem (St s₀) 16 = _
    rw [hm, bytes_write, h.state]
    rw [List.take_of_length_le (show (blks s₀).length ≤ N s₀ by simp [Spec.Cbc.blocksAt])]
    rfl

theorem correct_wp {s₀ : State} (hp : CPre s₀) :
    WP isa encrypt s₀ fun t => encContract.post s₀ t ∧ Frame [stR s₀, dataR s₀] s₀.mem t.mem := by
  have hN := (s₀.gpr .r8).isLt
  rw [encrypt]
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
    simp [encContract, VG.Proof.AesCbc.X86_64.cbcX86_64, modeX86_64, cbcMode, cbc, cts,
      hn, Spec.Cbc.blocksAt, Spec.Cbc.encrypt, Spec.Cbc.next, mem_arithFlags]
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    refine WP.seq (WP.mono (setup_ok hp rfl rfl rfl rfl) fun s₁ ⟨h₁, z₁⟩ => ?_)
    exact WP.seq (WP.mono (loops_ok hp (by omega_arith) h₁ z₁) fun s₂ h₂ => finish_ok hp h₂)

theorem keeps (r : Reg) (hr : r ∈ calleeSaved) : ∀ i ∈ instrs encrypt, Taint.clobbers i r = false := by
  have h : encrypt.allInstrs (fun i => calleeSaved.all fun r => !Taint.clobbers i r) = true := by
    decide +kernel
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  intro i hi
  simpa using List.all_eq_true.mp (h i hi) r hr

theorem correct (s : State) (hs : encContract.pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ encContract.post s s' := by
  have hp := CPre.of hs
  obtain ⟨t, s', he, hq, hf⟩ := correct_wp hp
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he
    ⟨fun r hr => Exec.gpr (keeps r hr) he, ?_⟩, hq⟩
  exact hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data) (by decide)

theorem ct : ConstantTime isa encContract.pre encContract.pub encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, h7⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- The contract of `Spec/Cbc/`'s signature, for any stack: `encContract`
asks nothing of it. -/
theorem implies0 : encContract.Implies (Proof.AesCbc.encryptRoundsContract X86_64.abi 0) := by
  sig_implies [Proof.AesCbc.encryptRoundsContract, Spec.Cbc.aesSig, encContract,
    VG.Proof.AesCbc.X86_64.cbcX86_64, modeX86_64, cbcMode, ciphOf, cbc, cts, X86_64.abi,
    X86_64.argRegs] [VG.Proof.AesCbc.X86_64.sat] using VG.Proof.AesCbc.X86_64.sat

theorem implies : encContract.Implies (Proof.AesCbc.encryptRoundsContract X86_64.abi 8) := by
  sig_implies [Proof.AesCbc.encryptRoundsContract, Spec.Cbc.aesSig, encContract,
    VG.Proof.AesCbc.X86_64.cbcX86_64, modeX86_64, cbcMode, ciphOf, cbc, cts, X86_64.abi,
    X86_64.argRegs] [VG.Proof.AesCbc.X86_64.sat] using VG.Proof.AesCbc.X86_64.sat

/-- With no stack below the return address: the code has no frame and no call. -/
theorem verified0 : Verified X86_64.target encrypt (Proof.AesCbc.encryptRoundsContract X86_64.abi 0) :=
  Verified.of_correct correct ct implies0

theorem verified : Verified X86_64.target encrypt (Proof.AesCbc.encryptRoundsContract X86_64.abi 8) :=
  Verified.of_correct correct ct implies

theorem written_of {stack : Nat} (himp : encContract.Implies (Proof.AesCbc.encryptRoundsContract X86_64.abi stack))
    (s : State) (tr : List Leak) (t : State)
    (hs : (Proof.AesCbc.encryptRoundsContract X86_64.abi stack).pre s) (he : Exec isa encrypt s tr t) :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Cbc.aesSig [("scratch", 0)] s t := by
  have hp := CPre.of (himp.pre s hs)
  obtain ⟨tr', t', he', _, hf⟩ := correct_wp hp
  obtain ⟨-, rfl⟩ := Exec.det he he'
  simp [Sig.writtenWithin, X86_64.abi, X86_64.argRegs, Abi.withConsts, Spec.Cbc.aesSig,
    Sig.words, Sig.arrays, Param.words, ArgWord.bits]
  intro i hi
  have hib : i < 2176 := by simpa [Elem.size] using hi
  exact hf _ fun r hr hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.iv_scr _ hc (Offset.contains_base _ (by omega_using [hib]) (by omega_using [hib]))
    · exact hp.data_scr _ hc (Offset.contains_base _ (by omega_using [hib]) (by omega_using [hib]))

theorem written (s : State) (tr : List Leak) (t : State)
    (hs : (Proof.AesCbc.encryptRoundsContract X86_64.abi 8).pre s) (he : Exec isa encrypt s tr t) :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Cbc.aesSig [("scratch", 0)] s t :=
  written_of implies s tr t hs he

end VG.Proof.AesCbc.X86_64.Encrypt

end

end

-- separate module: the parallel loop and memory proofs cost more to check than their imports.

/-! # CBC decryption: independent AES rounds, sequential chaining stores -/

@[expose] public section
namespace VG.Proof.AesCbc.X86_64.Decrypt
open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Aes.X86_64.AesNi
open VG.Impl.Aes.X86_64.AesNi (at_ regs8 loadData aesDec imcKeys blocksLoad)
open VG.Impl.AesCbc.X86_64.Decrypt
open VG.Spec.Aes (bytesAt)

/-- The processed prefix and the original unprocessed ciphertext. -/
def DataInv (m₀ m : Mem) (D : Addr) (n c : Nat) (F : Nat → Spec.Aes.State) : Prop :=
  ∀ k < n, Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16*k)) =
    if k < c then F k else Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16*k))

theorem original_word {m₀ m : Mem} {D : Addr} {n c k : Nat} {F : Nat → Spec.Aes.State}
    (h : DataInv m₀ m D n c F) (hk : k < n) (hc : c ≤ k) :
    m.readW (D + BitVec.ofNat 64 (16*k)) 128 = m₀.readW (D + BitVec.ofNat 64 (16*k)) 128 := by
  apply st_inj
  rw [← stateAt_eq, ← stateAt_eq, h k hk, ite_eq_right (by omega_arith)]

theorem data_write {m₀ m : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State} {v : BitVec 128}
    (hn : 16*n ≤ 2^64) (hc : c < n) (h : DataInv m₀ m D n c F) (hv : st v = F c) :
    DataInv m₀ (m.writeW (D + BitVec.ofNat 64 (16*c)) v) D n (c+1) F := by
  intro k hk
  by_cases he : k = c
  · subst he
    rw [stateAt_eq, Mem.readW_writeW_self _ _ 16 _ (by decide), hv, ite_eq_left (by omega_arith)]
  · rw [stateAt_eq, Mem.readW_writeW_sep (Offset.disjoint D (by omega_using [he]) (by omega_arith) (by omega_arith)) (by decide),
      ← stateAt_eq, h k hk]
    by_cases hlt : k < c
    · rw [ite_eq_left hlt, ite_eq_left (by omega_arith)]
    · rw [ite_eq_right hlt, ite_eq_right (by omega_using [hlt,he])]

theorem finish_ok (b : XReg) (j : Nat) (s : State) (hb : b ≠ .xmm15)
    (hin : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block (finish b j)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofNat 64 (16*j)) (s.xmm b ^^^ s.xmm .xmm15) ∧
      t.xmm .xmm15 = s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (16*j)) 128 ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.ymmHi = s.ymmHi ∧
      (∀ r, r ≠ b → r ≠ .xmm15 → t.xmm r = s.xmm r) := by
  rw [finish, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.AesCbc.X86_64.Encrypt.exec_load (by
    simp only [XOp.exec, rd_setXmm, wr_setXmm, gpr_setXmm]
    exact ⟨hin.choose, List.mem_append_right _ hin.choose_spec.1, hin.choose_spec.2⟩), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.AesCbc.X86_64.Encrypt.exec_store (by
    simp only [XOp.exec, wr_setXmm, gpr_setXmm]; exact hin), WP.block_nil ?_⟩
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, fun r h₁ h₂ => ?_⟩
  · simp only [XOp.exec, mem_setXmm, gpr_setXmm, xmm_setXmm_of_ne _ _ hb,
      xmm_setXmm_self, XBinOp.eval]
  · simp only [xmm_setXmm_self, XOp.exec, mem_setXmm, gpr_setXmm]
  · simp only [XOp.exec, xmm_setXmm_of_ne _ _ h₂, xmm_setXmm_of_ne _ _ h₁]

/-- A group is written in order, retaining each ciphertext for its successor. -/
theorem finishData_ok {m₀ : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State}
    {chain : Nat → BitVec 128} (hn : 16*n ≤ 2^64)
    (hnext : ∀ k < n, chain (k+1) = m₀.readW (D + BitVec.ofNat 64 (16*k)) 128) :
    ∀ (rs : List XReg) (j : Nat) (s : State), rs.Nodup → .xmm15 ∉ rs →
    s.gpr .rdx = D + BitVec.ofNat 64 (16*c) → c+j+rs.length ≤ n →
    (⟨D,16*n⟩ : Region) ∈ s.wr → DataInv m₀ s.mem D n (c+j) F →
    s.xmm .xmm15 = chain (c+j) →
    (∀ k (h : k < rs.length), st (s.xmm rs[k] ^^^ chain (c+j+k)) = F (c+j+k)) →
    WP isa (.block (finishData rs j)) s fun t =>
      DataInv m₀ t.mem D n (c+j+rs.length) F ∧ t.xmm .xmm15 = chain (c+j+rs.length) ∧
      Frame [⟨D,16*n⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.ymmHi = s.ymmHi ∧
      (∀ r, r ≠ .xmm15 → r ∉ rs → t.xmm r = s.xmm r)
  | [], _, s, _, _, _, _, _, hd, hx, _ =>
    WP.block_nil ⟨hd,hx,Frame.refl _ _,rfl,rfl,rfl,rfl,fun _ _ _ => rfl⟩
  | b::bs, j, s, hnd, h15, hg, hc, hw, hd, hx, hv => by
    have hb : b ≠ .xmm15 := fun h => h15 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h15' : .xmm15 ∉ bs := fun h => h15 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hc
    have addr : s.gpr .rdx + BitVec.ofNat 64 (16*j) = D + BitVec.ofNat 64 (16*(c+j)) := by
      rw [hg, Offset.add_add_eq D (c := 16*(c+j)) (by omega_arith)]
    rw [finishData, WP.block_append_iff]
    refine WP.mono (finish_ok b j s hb (by
      rw [addr]; exact ⟨_, hw, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
      fun t ⟨hm,hx',hg',hr,hw',yh,ho⟩ => ?_
    rw [addr] at hm hx'
    have hv0 : st (s.xmm b ^^^ s.xmm .xmm15) = F (c+j) := by
      rw [hx]; exact hv 0 (by simp)
    have hd' := data_write hn (by omega_arith) hd hv0
    rw [← hm] at hd'
    have hchain : t.xmm .xmm15 = chain (c+(j+1)) := by
      rw [hx', original_word hd (by omega_arith) (by omega_arith), ← hnext (c+j) (by omega_arith)]
      congr 1
    have hf : Frame [⟨D,16*n⟩] s.mem t.mem := by
      rw [hm]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    refine WP.mono (finishData_ok (m₀ := m₀) (D := D) (n := n) (c := c) (F := F) (chain := chain) hn hnext bs (j+1) t (List.nodup_cons.mp hnd).2 h15'
      (by rw [hg']; exact hg) (by omega_arith) (hw' ▸ hw) (by simpa [Nat.add_assoc] using hd') hchain
      (fun k hk => by
        rw [ho _ (fun h => hbs (h ▸ List.getElem_mem hk)) (fun h => h15' (h ▸ List.getElem_mem hk)),
          show c+(j+1)+k=c+j+(k+1) by omega_arith]
        exact hv (k+1) (by simp; omega_arith))) fun u ⟨hu,hx'',hf',hg'',hr',hw'',yh',ho'⟩ => ?_
    have he : c+(j+1)+bs.length = c+j+(b::bs).length := by simp; omega_arith
    rw [he] at hu hx''
    exact ⟨hu,hx'',hf.trans hf',hg''.trans hg',hr'.trans hr,hw''.trans hw',yh'.trans yh,fun r h₁ h₂ =>
      (ho' r h₁ (fun h => h₂ (List.mem_cons_of_mem _ h))).trans
        (ho r (fun h => h₂ (h ▸ List.mem_cons_self)) h₁)⟩

def chaining (s₀ : State) : Nat → BitVec 128
  | 0 => s₀.mem.readW (Iv s₀) 128
  | k+1 => s₀.mem.readW (blk s₀ k) 128

def output (s₀ : State) (k : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i =>
    (Spec.Aes.invCipher (R s₀) (wK s₀) (Spec.Aes.stateAt s₀.mem (blk s₀ k))).getD i.1 0 ^^^
      byte (chaining s₀ k) i.1

structure Inv (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ N s₀
  keys : DKeys (R s₀) (wK s₀) s
  rdi : s.gpr .rdi = W s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r8 : s.gpr .r8 = S s₀
  r10 : s.gpr .r10 = W s₀ + BitVec.ofNat 64 (16 * R s₀)
  r11 : s.gpr .r11 = Iv s₀
  rdx : s.gpr .rdx = blk s₀ p
  rcx : s.gpr .rcx = BitVec.ofNat 64 (N s₀-p)
  chain : s.xmm .xmm15 = chaining s₀ c
  data : DataInv s₀.mem s.mem (Dp s₀) (N s₀) c (output s₀)
  frame : Frame [dataR s₀, ⟨S s₀,224⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem keys_stable {s₀ s t : State} (hp : UPre s₀) (h : DKeys (R s₀) (wK s₀) s)
    (hdi : s.gpr .rdi = W s₀) (h8 : s.gpr .r8 = S s₀)
    (hg : t.gpr = s.gpr) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hf : Frame [dataR s₀] s.mem t.mem) : DKeys (R s₀) (wK s₀) t := by
  refine Ecb.dkeys_congr h (by rw [hg]) (by rw [hg]) hr hw ?_ ?_
  · rw [hdi]
    exact bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.sch_data.sub_left (Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega_arith))) (by
        rcases hp.rounds with h | h | h <;> omega_arith)
  · intro j h₁ h₂
    rw [h8, ofInt_natCast]
    exact hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 (16*j),16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_right (Offset.sub_base _ (by rcases hp.rounds with h | h | h <;> omega_arith))).symm) (by decide)

theorem group_ok {s₀ s : State} (hp : UPre s₀) (rs : List XReg)
    (hrs : rs = regs8 ∨ rs = [.xmm0]) {c : Nat} (hc : c+rs.length ≤ N s₀)
    (hI : Inv s₀ c c s) (after : List Instr) {Q : State → Prop}
    (hQ : ∀ t, Inv s₀ (c+rs.length) c t → WP isa (.block after) t Q) :
    WP isa (group rs after) s Q := by
  obtain ⟨hnd,h8⟩ := Ecb.regs_nodup rs hrs
  have h15 : .xmm15 ∉ rs := by rcases hrs with rfl | rfl <;> decide
  have hw := hp.data_wrap
  have addr (t : State) (ht : t.gpr .rdx = s.gpr .rdx) (k : Nat) :
      t.gpr .rdx + BitVec.ofInt 64 ((16*(0+k):Nat):Int) = blk s₀ (c+k) := by
    rw [ht,hI.rdx,ofInt_natCast,blk,blk,Offset.add_add_eq _ (c := 16*(c+k)) (by omega_arith)]
  have addr' (k : Nat) : s.gpr .rdx + BitVec.ofNat 64 (16*(0+k)) = blk s₀ (c+k) := by
    rw [← addr s rfl k,ofInt_natCast]
  refine WP.seq (WP.mono (loadData_ok rs 0 s hnd (fun k hk => by
    rw [addr s rfl k,hI.rd,hI.wr,hp.rd,hp.wr]
    exact ⟨dataR s₀,by simp,Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
    fun u ⟨hl,gl,ml,rl,wl,xl⟩ => ?_)
  have hku : DKeys (R s₀) (wK s₀) u :=
    hI.keys.of_frame ⟨gl,ml,rl,wl,xl⟩
  refine WP.seq (WP.mono (aesDec_ok rs hnd h8 hp.rounds u hku
    (by rw [gl,hI.rsi]; simp) (by rw [gl,hI.r10,hI.rdi])) fun v ⟨ha,fa⟩ => ?_)
  have gv : v.gpr = s.gpr := fa.gpr.trans gl
  have mv : v.mem = s.mem := fa.mem.trans ml
  have hx : v.xmm .xmm15 = chaining s₀ c := by rw [fa.xmm _ (by simp [h15]),xl _ h15,hI.chain]
  rw [WP.block_append_iff]
  refine WP.mono (finishData_ok (m₀ := s₀.mem) (D := Dp s₀) (n := N s₀) (c := c)
    (F := output s₀) (chain := chaining s₀) (by omega_arith) (fun _ _ => rfl) rs 0 v hnd h15
    (by rw [gv,hI.rdx]) (by simpa using hc)
    (by rw [fa.wr,wl,hI.wr,hp.wr]; simp) (by simpa [mv] using hI.data)
    (by simpa using hx) (fun k hk => by
      have he := ha _ (List.getElem_mem hk)
      rw [hl k hk,← ofInt_natCast (16*(0+k))] at he
      rw [addr s rfl k,hI.data _ (by omega_arith),ite_eq_right (by omega_arith)] at he
      apply st_ext
      intro i hi
      rw [getD_st _ hi,byte_xor,← getD_st _ hi,he]
      change _ = (Vector.ofFn fun i =>
        (Spec.Aes.invCipher (R s₀) (wK s₀) (Spec.Aes.stateAt s₀.mem (blk s₀ (c+0+k)))).getD i.1 0 ^^^
          byte (chaining s₀ (c+0+k)) i.1).getD i 0
      rw [getD_ofFn hi]; rfl)) fun t ⟨hd,hchain,hf,hg,hr,hw,_,ho⟩ => ?_
  have gt : t.gpr = s.gpr := hg.trans gv
  have rt : t.rd = s.rd := hr.trans (fa.rd.trans rl)
  have wt : t.wr = s.wr := hw.trans (fa.wr.trans wl)
  rw [mv] at hf
  refine hQ t ⟨hc,keys_stable hp hI.keys hI.rdi hI.r8 gt rt wt hf,
    by rw [gt]; exact hI.rdi,by rw [gt]; exact hI.rsi,by rw [gt]; exact hI.r8,
    by rw [gt]; exact hI.r10,by rw [gt]; exact hI.r11,by rw [gt]; exact hI.rdx,
    by rw [gt]; exact hI.rcx,by simpa using hchain,by simpa using hd,
    hI.frame.trans (hf.mono (by simp)),rt.trans hI.rd,wt.trans hI.wr⟩

/-- The eight-block body. -/
theorem body8_ok {s₀ : State} (hp : UPre s₀) {c : Nat} (hc : c + 8 ≤ N s₀) {s : State} (hI : Inv s₀ c c s) :
    WP isa blocks8 s fun s' => Inv s₀ (c + 8) (c + 8) s' ∧
      s'.cf = some (decide (N s₀ - (c + 8) < 8)) := by
  have hn : 16*N s₀ ≤ 2^64 := by have := hp.data_wrap; omega_arith
  refine group_ok hp regs8 (.inl rfl) hc hI _ fun s₁ hI₁ => ?_
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hrdx := hI₁.rdx
  have hrcx := hI₁.rcx
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8, hrdx, hrcx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (N s₀ - c) - 8 = BitVec.ofNat 64 (N s₀ - (c + 8)) := by
    have := (s₀.gpr .rcx).isLt; bv_omega
  refine ⟨{ hI₁ with
    keys := Ecb.dkeys_congr hI₁.keys (by simp) (by simp) rfl rfl rfl (fun _ _ _ => rfl)
    rdi := by simp [hI₁.rdi]
    rsi := by simp [hI₁.rsi]
    r8 := by simp [hI₁.r8]
    r11 := by simp [hI₁.r11]
    r10 := by simp [hI₁.r10]
    rdx := by simp only [reduceCtorEq, ↓reduceIte, blk]; bv_omega
    rcx := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - (c + 8) < 2 ^ 64 by omega_arith),
    show (8 : BitVec 64).toNat = 8 from rfl]

/-- The one-block body. -/
theorem body1_ok {s₀ : State} (hp : UPre s₀) {c : Nat} (hc : c < N s₀) {s : State} (hI : Inv s₀ c c s) :
    WP isa blocks1 s fun s' => Inv s₀ (c + 1) (c + 1) s' ∧
      s'.zf = some (decide (N s₀ - (c + 1) = 0)) := by
  have hn : 16*N s₀ ≤ 2^64 := by have := hp.data_wrap; omega_arith
  refine group_ok hp [.xmm0] (.inr rfl) hc hI _ fun s₁ hI₁ => ?_
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have hrdx := hI₁.rdx
  have hrcx := hI₁.rcx
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e16, e1, hrdx, hrcx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (N s₀ - c) - 1 = BitVec.ofNat 64 (N s₀ - (c + 1)) := by
    have := (s₀.gpr .rcx).isLt; bv_omega
  refine ⟨{ hI₁ with
    keys := Ecb.dkeys_congr hI₁.keys (by simp) (by simp) rfl rfl rfl (fun _ _ _ => rfl)
    rdi := by simp [hI₁.rdi]
    rsi := by simp [hI₁.rsi]
    r8 := by simp [hI₁.r8]
    r11 := by simp [hI₁.r11]
    r10 := by simp [hI₁.r10]
    rdx := by simp only [reduceCtorEq, ↓reduceIte, blk]; bv_omega
    rcx := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  rw [hsub, Ecb.beq_ofNat_zero' (by omega_arith)]

theorem test_ok {s₀ : State} (hp : UPre s₀) {c : Nat} {s : State} (hI : Inv s₀ c c s) :
    WP isa (.block [.alu .test .rcx (.reg .rcx)]) s fun s' =>
      Inv s₀ c c s' ∧ s'.zf = some (decide (N s₀ - c = 0)) := by
  have hn : 16*N s₀ ≤ 2^64 := by have := hp.data_wrap; omega_arith
  have hrcx := hI.rcx
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, hrcx, BitVec.and_self, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨{ hI with keys := hI.keys.of_frame (rs := []) ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩ },
    by rw [Ecb.beq_ofNat_zero' (by omega_arith)]⟩

/-- The blocks left after `c`, eight and then one at a time. -/
theorem tail_ok {s₀ : State} (hp : UPre s₀) {c₀ : Nat} {s₁ : State} (hI₁ : Inv s₀ c₀ c₀ s₁)
    (hcf : s₁.cf = some (decide (N s₀ - c₀ < 8))) :
    WP isa tail s₁ (Inv s₀ (N s₀) (N s₀)) := by
  have hn : 16*N s₀ ≤ 2^64 := by have := hp.data_wrap; omega_arith
  refine WP.seq (WP.mono (Q := fun s => ∃ c, N s₀ - c < 8 ∧ Inv s₀ c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (N s₀ - c₀ < 8)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c₀, by simpa using h, hI₁⟩
    · let I8 : Nat → State → Prop := fun m s => ∃ c, m = N s₀ - c ∧ c + 8 ≤ N s₀ ∧ Inv s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa blocks8 s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, N s₀ - c < 8 ∧ Inv s₀ c c s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, I8 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (body8_ok hp hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : N s₀ - (c + 8) < 8
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 8, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (c + 8), by omega_arith, c + 8, rfl, by omega_arith, hI'⟩
      exact WP.loop (M := isa) I8 hstep (N s₀ - c₀) s₁ ⟨c₀, rfl, by simp at h; omega_arith, hI₁⟩
  refine WP.seq (WP.mono (test_ok hp hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.ite (decide (N s₀ - c = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = N s₀ := by have := hI₃.le; simp at h; omega_arith
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = N s₀ - c ∧ c < N s₀ ∧ Inv s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa blocks1 s (fun s' =>
        (eval .ne s' = some false ∧ Inv s₀ (N s₀) (N s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (body1_ok hp hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : N s₀ - (c + 1) = 0
      · have : c + 1 = N s₀ := by omega_arith
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], N s₀ - (c + 1), by omega_arith, c + 1, rfl, by omega_arith, hI'⟩
    have hlt : c < N s₀ := by have := hI₃.le; simp at h; omega_arith
    exact WP.loop (M := isa) I1 hstep (N s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩

def adapted (s : State) : State :=
  ((((s.setReg .r11 (s.gpr .rdx)).setReg .rdx (s.gpr .rcx)).setReg .rcx (s.gpr .r8)).setReg
    .r8 (s.gpr .r9)).setXmm .xmm15 (s.mem.readW (s.gpr .rdx) 128)

theorem adapt_ok {s : State} (hp : UPre s) : WP isa (.block adapt) s (fun t => t = adapted s) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rdx) 16 := by
    rw [hp.rd,hp.wr]
    exact ⟨ivR s,by simp,Region.contains_self _ _⟩
  have haz (p : Addr) : p + BitVec.ofInt 64 ((0 : Nat) : Int) = p := by bv_omega
  apply WP.of_runBlock
  simp only [adapt,runBlock_cons,runStep_some,runBlock_nil,exec,isa,readSrc,Option.map_some,
    at_,State.ea,gpr_setReg,mem_setReg,rd_setReg,wr_setReg,reduceCtorEq,ite_true,ite_false,
    haz,State.load128,hin,Option.some.injEq,exists_eq_left']
  rfl

theorem setup_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (.seq (.block adapt) (.seq imcKeys (.block blocksLoad))) s₀ fun s =>
      Inv s₀ 0 0 s ∧ s.cf = some (decide (N s₀ < 8)) := by
  refine WP.seq (WP.mono (adapt_ok hp) fun a ha => ?_)
  subst ha
  let a := adapted s₀
  have ga : ∀ r, a.gpr r = (match r with
      | .r11 => Iv s₀ | .rdx => Dp s₀ | .rcx => s₀.gpr .r8 | .r8 => S s₀ | _ => s₀.gpr r) := by
    intro r
    simp only [a,adapted,gpr_setXmm,gpr_setReg]
    cases r <;> rfl
  have ma : a.mem = s₀.mem := by simp only [a,adapted,mem_setXmm,mem_setReg]
  have ra : a.rd = s₀.rd := rfl
  have wa : a.wr = s₀.wr := rfl
  have hs : InRegions a.wr (a.gpr .r8) 2048 := by
    rw [wa,ga,hp.wr]
    exact ⟨scrR s₀,by simp,by simpa using Offset.contains_base (S s₀) (d := 0) (n := 2048) (k := 2176) (by decide) (by decide)⟩
  have hsep : (⟨a.gpr .rdi,240⟩ : Region).Disjoint ⟨a.gpr .r8,2048⟩ := by
    simp only [ga]; exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  have hK : Keys (R s₀) (wK s₀) a := by
    refine ⟨?_,by rcases hp.rounds with h | h | h <;> omega_arith,?_⟩
    · rw [ma,ga]
    · intro j hj
      rw [ra,wa,ga,hp.rd,hp.wr,ofInt_natCast]
      exact ⟨schR s₀,by simp,Offset.contains_base _ (by rcases hp.rounds with h | h | h <;> omega_arith) (by
        rcases hp.rounds with h | h | h <;> omega_arith)⟩
  refine WP.seq (WP.mono (imcKeys_ok hp.rounds (by rw [ga]; exact rsi_ofNat s₀) hs
    (by rw [ga,ra,wa,hp.rd,hp.wr]; simp) hsep) fun u ⟨js,hi,hjs⟩ => ?_)
  have hD := dKeys_of_imc hK hs hsep hi hjs
  refine WP.mono (Ecb.blocksLoad_ok u) fun v ⟨h10,hg,hm,hr,hw,hx,hcf⟩ => ?_
  have hg' (r : Reg) (hn : r ≠ .r10) : v.gpr r = a.gpr r := by rw [hg r hn,hi.gpr]
  have frameU : Frame [dataR s₀,⟨S s₀,224⟩] s₀.mem u.mem := by
    have hf := hi.lo
    rw [ma,ga] at hf
    exact hf.mono (by simp)
  have keysV : DKeys (R s₀) (wK s₀) v :=
    Ecb.dkeys_congr hD (hg _ (by decide)) (hg _ (by decide)) hr hw
      (by rw [hm]) (fun _ _ _ => by rw [hm])
  refine ⟨⟨Nat.zero_le _,keysV,by rw [hg' _ (by decide),ga],by rw [hg' _ (by decide),ga],
    by rw [hg' _ (by decide),ga],?_,by rw [hg' _ (by decide),ga],?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · rw [h10,hi.gpr,ga,ga]
  · rw [hg' _ (by decide),ga]; simp [blk]
  · rw [hg' _ (by decide),ga]; simp [N]
  · rw [hx,hi.xmm _ (by decide)]
    rfl
  · intro k hk
    rw [hm]
    have hd : (⟨blk s₀ k,16⟩ : Region).Disjoint ⟨S s₀,2048⟩ :=
      (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
    rw [stateAt_eq,stateAt_eq]
    have hf := hi.frame
    rw [ma,ga] at hf
    rw [hf.readW (r := ⟨blk s₀ k,16⟩) (Region.contains_self _ _)
      (by simpa using hd) (by decide),ite_eq_right (Nat.not_lt_zero _)]
  · rw [hm]; exact frameU
  · rw [hr,hi.rd,ra]
  · rw [hw,hi.wr,wa]
  · rw [hcf,hi.gpr,ga]

theorem list_getD {α : Type} {xs : List α} {k : Nat} {d : α} (hk : k < xs.length) :
    xs.getD k d = xs[k] := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some]

theorem vector_listD (v : Spec.Aes.State) (i : Nat) (hi : i < 16) :
    v.toList.getD i 0 = v.getD i 0 := by
  rw [list_getD (by simpa using hi),Vector.getElem_toList]
  simp [Vector.getD,hi]

theorem chaining_bytes (s₀ : State) (k : Nat) (hk : k ≤ N s₀) :
    (st (chaining s₀ k)).toList = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
  cases k with
  | zero => simp only [chaining,← stateAt_eq,List.take_zero]; exact (bytesAt_toList _ _).symm
  | succ k =>
    rw [next_take_succ _ _ k (by rw [length_blocksAt]; omega_using [hk]),
      list_getD (by rw [length_blocksAt]; omega_using [hk]),getElem_blocksAt (hk := by omega_using [hk])]
    exact (congrArg Vector.toList (stateAt_eq _ _).symm).trans (bytesAt_toList _ _).symm

theorem block_bytes (s₀ : State) (k : Nat) (hk : k < N s₀) :
    (output s₀ k).toList =
      (Spec.Cbc.decrypt (Spec.Cbc.aesInvWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀)).getD k [] := by
  rw [decrypt_getD _ _ _ k (by rw [length_blocksAt]; exact hk),
    list_getD (by rw [length_blocksAt]; exact hk),getElem_blocksAt (hk := hk),
    aesInvWith_state,← chaining_bytes _ _ (Nat.le_of_lt hk)]
  apply Proof.Cmac.ext16 (by simp) (by simp [Spec.Cbc.xor])
  intro i hi
  rw [vector_listD _ _ hi]
  rw [xor_eq,Proof.Cmac.getD_xor (by simp) (by simpa using hi)]
  rw [vector_listD _ _ hi,vector_listD _ _ hi]
  rw [getD_st _ hi]
  exact getD_ofFn hi

theorem data_done {s₀ : State} {m : Mem}
    (hd : DataInv s₀.mem m (Dp s₀) (N s₀) (N s₀) (output s₀)) :
    Spec.Cbc.blocksAt m (Dp s₀) (N s₀) =
      Spec.Cbc.decrypt (Spec.Cbc.aesInvWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀) := by
  apply List.ext_getElem
  · simp [length_decrypt,length_blocksAt]
  · intro k hk _
    have hk' : k < N s₀ := by simpa [length_blocksAt] using hk
    rw [getElem_blocksAt _ _ hk',bytesAt_toList,hd k hk',ite_eq_left hk',block_bytes _ _ hk',
      list_getD (by simp [length_decrypt,length_blocksAt]; exact hk')]

theorem finish_wp {s₀ s : State} (hp : UPre s₀) (hI : Inv s₀ (N s₀) (N s₀) s) :
    WP isa (.block [.movdquStore (at_ .r11 0) .xmm15]) s fun t =>
      (cbcX86_64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀,⟨S s₀,224⟩] s₀.mem t.mem := by
  rw [WP.block_cons_iff]
  refine ⟨_,VG.Proof.AesCbc.X86_64.Encrypt.exec_store (by
    rw [hI.wr,hI.r11,hp.wr,BitVec.add_zero]
    exact ⟨ivR s₀,by simp,Region.contains_self _ _⟩),WP.block_nil ?_⟩
  have fs : Frame [ivR s₀] s.mem (s.mem.writeW (Iv s₀) (s.xmm .xmm15)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  simp only [hI.r11,BitVec.add_zero]
  refine ⟨⟨?_,?_⟩,(hI.frame.mono (by simp)).trans (fs.mono (by simp))⟩
  · change Spec.Cbc.blocksAt (s.mem.writeW (Iv s₀) (s.xmm .xmm15)) (Dp s₀) (N s₀) = _
    have hb : Spec.Cbc.blocksAt (s.mem.writeW (Iv s₀) (s.xmm .xmm15)) (Dp s₀) (N s₀) =
        Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) := by
      apply List.map_congr_left
      intro k hk
      exact bytesAt_frame fs (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.iv_data.symm.sub_left (UPre.data_sub (List.mem_range.mp hk))) (by decide)
    rw [hb,data_done hI.data]
    rfl
  · change bytesAt (s.mem.writeW (Iv s₀) (s.xmm .xmm15)) (Iv s₀) 16 = _
    rw [← VG.Proof.AesCbc.X86_64.Encrypt.bytes_read,Mem.readW_writeW_self _ _ 16 _ (by decide),hI.chain]
    change (st (chaining s₀ (N s₀))).toList = _
    rw [chaining_bytes _ _ (Nat.le_refl _),List.take_of_length_le (by simp [Spec.Cbc.blocksAt])]
    rfl

theorem correct_wp {s₀ : State} (hp : UPre s₀) : WP isa decrypt s₀ fun t =>
    (cbcX86_64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀,⟨S s₀,224⟩] s₀.mem t.mem := by
  change WP isa (.seq (.seq (.block adapt) (.seq imcKeys (.block blocksLoad)))
    (.seq tail (.block [.movdquStore (at_ .r11 0) .xmm15]))) s₀ _
  refine WP.seq (WP.mono (setup_ok hp) fun s ⟨hI,hcf⟩ => ?_)
  refine WP.seq (WP.mono (tail_ok hp hI (by simpa using hcf)) fun s' hI' => finish_wp hp hI')

theorem keeps (r : Reg) (hr : r ∈ calleeSaved) : ∀ i ∈ instrs decrypt, Taint.clobbers i r = false := by
  have h : decrypt.allInstrs (fun i => calleeSaved.all fun r => !Taint.clobbers i r) = true := by
    decide +kernel
  rw [Code.allInstrs_eq,List.all_eq_true] at h
  intro i hi
  simpa using List.all_eq_true.mp (h i hi) r hr

theorem correct (s : State) (hs : (cbcX86_64 false).pre s) :
    ∃ tr t, Exec isa decrypt s tr t ∧ abiPreserved s t ∧ (cbcX86_64 false).post s t := by
  have hp := UPre.of hs
  obtain ⟨tr,t,he,hq,hf⟩ := correct_wp hp
  refine ⟨tr,t,he,abiPreserved_of_exec (by decide +kernel) he
    ⟨fun r hr => Exec.gpr (keeps r hr) he,?_⟩,hq⟩
  exact hf.readW (r := ⟨s.gpr .rsp,8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_scr.sub_right (Region.sub_prefix (by decide))) (by decide)

theorem ct : ConstantTime isa (cbcX86_64 false).pre (cbcX86_64 false).pub decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx,.r8,.r9,.rsp])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1,h2,h3,h4,h5,h6,h7⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem implies : (cbcX86_64 false).Implies (Proof.AesCbc.decryptRoundsContract X86_64.abi 8) := by
  sig_implies [Proof.AesCbc.decryptRoundsContract,Spec.Cbc.aesSig,cbcX86_64,modeX86_64,cbcMode,
    ciphOf,cbc,cts,X86_64.abi,X86_64.argRegs] [sat] using sat

theorem verified : Verified X86_64.target decrypt (Proof.AesCbc.decryptRoundsContract X86_64.abi 8) :=
  Verified.of_correct correct ct implies

theorem written (s : State) (tr : List Leak) (t : State)
    (hs : (Proof.AesCbc.decryptRoundsContract X86_64.abi 8).pre s) (he : Exec isa decrypt s tr t) :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Cbc.aesSig [("scratch",224)] s t := by
  have hp := UPre.of (implies.pre s hs)
  obtain ⟨tr',t',he',_,hf⟩ := correct_wp hp
  obtain ⟨-,rfl⟩ := Exec.det he he'
  simp [Sig.writtenWithin,X86_64.abi,X86_64.argRegs,Abi.withConsts,Spec.Cbc.aesSig,
    Sig.words,Sig.arrays,Param.words,ArgWord.bits]
  intro i hi hlo
  have hib : i < 2176 := by simpa [Elem.size] using hlo
  exact hf _ fun r hr hc => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.iv_scr _ hc (Offset.contains_base _ (by omega_using [hib]) (by omega_using [hib]))
    · exact hp.data_scr _ hc (Offset.contains_base _ (by omega_using [hib]) (by omega_using [hib]))
    · change (S s + BitVec.ofNat 64 i - S s).toNat + 1 ≤ 224 at hc
      rw [Offset.add_sub_cancel_left,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [hib])] at hc
      omega_using [hi, hc]

end VG.Proof.AesCbc.X86_64.Decrypt

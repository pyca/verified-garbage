module

public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Impl.AesCbc.X86_64.Encrypt
public import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
public import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
import VerifiedGarbage.Proof.AesCbc.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateLoop
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Blocks
meta import VerifiedGarbage.Impl.CmacAes.X86_64.AesNi
meta import VerifiedGarbage.Impl.AesCbc.X86_64.Encrypt
meta import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
meta import VerifiedGarbage.Spec.Cmac.Contract
meta import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateLoop
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

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

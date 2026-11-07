module

public import VerifiedGarbage.Impl.Modes.Arm.SeqFinal
public import VerifiedGarbage.Proof.Modes.Arm.SeqBody
public import VerifiedGarbage.Spec.Cfb.Final
public import VerifiedGarbage.Spec.Ofb.Final
import VerifiedGarbage.Proof.Modes.Arm.SeqLoop
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.FbFinal
import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.CmacAes.Arm.Words
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# CFB and OFB of a message's last piece on ARMv7: the contract and its proof

`seqFinalArm c S M`: the contract `Core.seqFinal c M` meets, for any core
`c` (with `S : CoreSpec c`) and mode `M` whose operations are all after a
call on the chaining block (`FinalOk`), on `seq`'s arguments with `len`
bytes of data (the precondition is `seqArm`'s for data a byte at a time,
`byteMode`). With `n = len / L` whole blocks and `r = len % L` bytes after
them: the whole blocks become `runSeq`'s, the `r` bytes are XORed with the
first bytes of `CIPH_K` of the chaining block `runSeq` leaves, and the IV
becomes that chaining block if `r = 0`, and its image under the cipher
otherwise (`seqFinal_wp`). `cfbEncFinal_post` and `cfbDecFinal_post` state
this as the specification's (`Spec.Cfb.EncryptFinal`, `DecryptFinal`) for
`cfbEnc` and `cfbDecF`, and `ofbFinal_post` as `Spec.Ofb.CryptFinal` for
`ofb`.

The prologue is `seq`'s (`prologue_wp`), and its invariant for no element
gives the loop's for no whole block (`FInv`): the registers hold the
arguments (`r6` the next segment, `r7` the bytes left), the first `k` blocks
are `runSeq`'s and the rest and the `r` bytes after them unchanged. A
segment (`seg_ok`) calls the core on the chaining block; then if a whole
block is left, the mode's operations (`opsCode_wp`) make block `k` and the
chaining and spare blocks `stepOf`'s, as in `seq`'s body, and if fewer are
left, `xorLoop_wp` XORs the chaining block's first bytes into them (`FDone`).
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf over over_frame)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add wp_subs wp_cmp wp_ldr wp_ldrb wp_strb op2_imm op2_reg op2_lsr cmp0
  ofNat_shr eval_eq eval_ne ofNat_beq_zero)

/-- The mode of the final function's precondition: the data a byte at a time
(`ds = 1`), so that `seqArm`'s precondition gives it `len` bytes, and the IV
written. -/
def byteMode : Mode := { pre := [], tgt := .o, post := [], finish := true, byte := true }

theorem ds_byteMode (c : Core) : c.ds byteMode = 1 := rfl

/-- A mode the final function runs: every operation after a call on the
chaining block, on two different blocks, a block at a time, the chaining
block returned in the IV; and blocks of `2 ^ lg` bytes. -/
structure FinalOk (c : Core) (M : Mode) : Prop where
  pre : M.pre = []
  tgt : M.tgt = .o
  byte : M.byte = false
  post : M.post.all (opOk c.bs false) = true
  fin : M.finish = true
  lg : 2 ^ c.lg = c.bs
  lg1 : 1 ≤ c.lg
  lg31 : c.lg ≤ 31

section
variable (c : Core) (S : CoreSpec c)

/-- `Core.seqFinal c M`, on `seq`'s arguments with `len` bytes of data. -/
def seqFinalArm (M : Mode) : Contract isa where
  pre := (seqArm c S byteMode).pre
  post s s' :=
    let len := (nArg c s).toNat
    let D := State.addr (dArg c s)
    let ciph := S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)
    let r := runSeq M ciph ⟨[], bytesAt s.mem (State.addr (ivArg c s)) c.bs,
        bytesAt s.mem (State.addr (scArg c s) + BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
      (blocksOf c.bs s.mem D (len / c.bs))
    blocksOf c.bs s'.mem D (len / c.bs) = r.1 ∧
      bytesAt s'.mem (D + BitVec.ofNat 64 (c.bs * (len / c.bs))) (len % c.bs) =
        Spec.Cbc.xor (bytesAt s.mem (D + BitVec.ofNat 64 (c.bs * (len / c.bs))) (len % c.bs)) (ciph r.2.o) ∧
      bytesAt s'.mem (State.addr (ivArg c s)) c.bs = if len % c.bs = 0 then r.2.o else ciph r.2.o
  pub := (seqArm c S byteMode).pub

end

section
variable (c : Core) {c' : Core} (S : CoreSpec c') (s₀ : State)

/-- The whole blocks. -/
abbrev nF : Nat := N c s₀ / c.bs
/-- The bytes after them. -/
abbrev rF : Nat := N c s₀ % c.bs
/-- The whole blocks on entry. -/
abbrev xsF : List (List Byte) := blocksOf c.bs s₀.mem (State.addr (Dp c s₀)) (nF c s₀)
/-- The address of the bytes after them. -/
abbrev tailA : Addr := State.addr (Dp c s₀) + BitVec.ofNat 64 (c.bs * nF c s₀)
/-- The mode after the first `k` blocks. -/
abbrev rKF (M : Mode) (k : Nat) : List (List Byte) × Blks := runSeq M (ciph S s₀) (b0 c' s₀) ((xsF c' s₀).take k)
/-- The data. -/
abbrev dataF : Region := dataR c s₀ byteMode

end

/-- The loop invariant, after `k` whole blocks. -/
structure FInv (c : Core) (S : CoreSpec c) (M : Mode) (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = Kp s₀
  r5 : s.gpr .r5 = Ivp c s₀
  r6 : s.gpr .r6 = Dp c s₀ + BitVec.ofNat 32 (c.bs * k)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (N c s₀ - c.bs * k)
  r8 : s.gpr .r8 = Sc c s₀
  r11 : c.rounds = true → s.gpr .r11 = Rp s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : k ≤ nF c s₀
  frame : Frame [dataF c s₀, blkR c s₀, belowR S s₀] (savedMem c s₀) s.mem
  data : blocksOf c.bs s.mem (State.addr (Dp c s₀)) (nF c s₀) = (rKF S s₀ M k).1 ++ (xsF c s₀).drop k
  tail : bytesAt s.mem (tailA c s₀) (rF c s₀) = bytesAt s₀.mem (tailA c s₀) (rF c s₀)
  o : bytesAt s.mem (oA c s₀) c.bs = (rKF S s₀ M k).2.o
  t : bytesAt s.mem (tA c s₀) c.bs = (rKF S s₀ M k).2.t

/-- After the loop. -/
structure FDone (c : Core) (S : CoreSpec c) (M : Mode) (s₀ : State) (s : State) : Prop where
  r5 : s.gpr .r5 = Ivp c s₀
  r8 : s.gpr .r8 = Sc c s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataF c s₀, blkR c s₀, belowR S s₀] (savedMem c s₀) s.mem
  data : blocksOf c.bs s.mem (State.addr (Dp c s₀)) (nF c s₀) = (rKF S s₀ M (nF c s₀)).1
  tail : bytesAt s.mem (tailA c s₀) (rF c s₀) =
    Spec.Cbc.xor (bytesAt s₀.mem (tailA c s₀) (rF c s₀)) (ciph S s₀ (rKF S s₀ M (nF c s₀)).2.o)
  o : bytesAt s.mem (oA c s₀) c.bs =
    if rF c s₀ = 0 then (rKF S s₀ M (nF c s₀)).2.o else ciph S s₀ (rKF S s₀ M (nF c s₀)).2.o

/-! ## Bytes -/

theorem byte_of_blocksOf1 {m m' : Mem} {D : Addr} {n : Nat} (h : blocksOf 1 m D n = blocksOf 1 m' D n) {i : Nat}
    (hi : i < n) : m (D + BitVec.ofNat 64 i) = m' (D + BitVec.ofNat 64 i) := by
  have e := congrArg (fun l => l[i]?) h
  simpa [VG.Proof.Modes.blocksOf, bytesAt, hi] using e

theorem bytesAt_congr_of {m m' : Mem} {D : Addr} {n : Nat}
    (h : ∀ i < n, m (D + BitVec.ofNat 64 i) = m' (D + BitVec.ofNat 64 i)) {a l : Nat} (hl : a + l ≤ n) :
    bytesAt m (D + BitVec.ofNat 64 a) l = bytesAt m' (D + BitVec.ofNat 64 a) l :=
  List.map_congr_left fun i hi => by
    have := List.mem_range.mp hi
    rw [VG.Offset.add_add]
    exact h _ (by omega)

theorem blocksOf_congr_of {m m' : Mem} {D : Addr} {n : Nat}
    (h : ∀ i < n, m (D + BitVec.ofNat 64 i) = m' (D + BitVec.ofNat 64 i)) {L k : Nat} (hk : L * k ≤ n) :
    blocksOf L m D k = blocksOf L m' D k :=
  List.map_congr_left fun j hj => by
    have := VG.Proof.Modes.idx_lt (L := L) (List.mem_range.mp hj)
    exact bytesAt_congr_of h (by omega)

theorem rKF_zero {c : Core} (S : CoreSpec c) (M : Mode) (s₀ : State) : rKF S s₀ M 0 = ([], b0 c s₀) := by
  simp only [rKF, List.take_zero, runSeq]

theorem rK_zero {c : Core} (S : CoreSpec c) (M : Mode) (s₀ : State) : rK S s₀ M 0 = ([], b0 c s₀) := by
  simp only [rK, List.take_zero, runSeq]

theorem nF_le (c : Core) (s₀ : State) : c.bs * nF c s₀ ≤ N c s₀ := Nat.mul_div_le _ _

theorem nF_rF (c : Core) (s₀ : State) : c.bs * nF c s₀ + rF c s₀ = N c s₀ := Nat.div_add_mod _ _

/-- The invariant for no element of `seq`'s prologue, for the data a byte at
a time, is the loop's for no whole block. -/
theorem FInv.of_linv {c : Core} {S : CoreSpec c} {M : Mode} {s₀ s : State} (h : LInv c S byteMode s₀ 0 s) :
    FInv c S M s₀ 0 s := by
  have hd := h.data
  rw [rK_zero, List.drop_zero, List.nil_append] at hd
  have hb : ∀ i < N c s₀, s.mem (State.addr (Dp c s₀) + BitVec.ofNat 64 i) =
      s₀.mem (State.addr (Dp c s₀) + BitVec.ofNat 64 i) := fun i hi =>
    byte_of_blocksOf1 (m := s.mem) (m' := s₀.mem) hd hi
  refine ⟨h.r4, h.r5, by rw [h.r6, Nat.mul_zero, Nat.mul_zero], by rw [h.r7, Nat.mul_zero], h.r8, h.r11, h.sp,
    h.rd, h.wr, Nat.zero_le _, h.frame, ?_, bytesAt_congr_of hb (by have := nF_rF c s₀; omega), ?_, ?_⟩
  · rw [rKF_zero, List.drop_zero, List.nil_append]
    exact blocksOf_congr_of hb (nF_le c s₀)
  · rw [h.o, rK_zero, rKF_zero]
  · rw [h.t, rK_zero, rKF_zero]

/-! ## The call on the chaining block -/

/-- What the arguments of a call on the chaining block leave, from `s`
with the schedule `K` in `r4`, the scratch buffer `Sb` in `r8` and the
number of rounds `R` (if any) in `r11`. -/
structure ArgsA (c : Core) (K R Sb : BitVec 32) (s s₂ : State) : Prop where
  regs : ∀ x, x ≠ .r0 → x ≠ .r1 → x ≠ .r2 → x ≠ .r3 → x ≠ .r12 → s₂.gpr x = s.gpr x
  r0 : s₂.gpr .r0 = K
  r1 : c.rounds = true → s₂.gpr .r1 = R
  rD : s₂.gpr c.dReg = Sb + BitVec.ofNat 32 oOff
  rN : s₂.gpr c.nReg = 1
  a3 : ∀ k, c.arg3 = some k → s₂.gpr .r3 = BitVec.ofNat 32 k
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  sp : s₂.sp = s.sp
  mem : s₂.mem = s.mem
  r12 : c.stackScratch ≠ 0 → s₂.gpr .r12 = Sb + BitVec.ofNat 32 c.csOff

theorem callArgsO_wp {c : Core} (S : CoreSpec c) {s : State} {K R Sb : BitVec 32} (h4 : s.gpr .r4 = K)
    (h8 : s.gpr .r8 = Sb) (h11 : c.rounds = true → s.gpr .r11 = R) :
    WP isa (.block (c.callArgs .o)) s (ArgsA c K R Sb s) := by
  have enc : encodable (BitVec.ofNat 32 oOff) = true := by
    show encodable (BitVec.ofNat 32 40) = true; decide
  simp only [Core.callArgs, mov, Core.base]
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => ?_
  have bt₂ : s₂.gpr .r8 + BitVec.ofNat 32 oOff = Sb + BitVec.ofNat 32 oOff := by
    rw [u₂.other _ (by decide), h8]
  cases hr : c.rounds
  · have hD : c.dReg = .r1 := by unfold Core.dReg; rw [hr]; rfl
    have hN : c.nReg = .r2 := by unfold Core.nReg; rw [hr]; rfl
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, hD, hN]
    refine wp_add (op2_imm enc) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ =>
      WP.block_append_iff.2 (arg3_wp S fun s₄' g₄ _ a₄ rd₄ wr₄ sp₄ m₄ => scrArg_wp S
      (by rw [g₄ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h8])
      fun s₅ g₅ c₅ rd₅ wr₅ sp₅ m₅ =>
      ⟨fun x a b d e i => ?_, ?_, fun h => absurd h (by simp [hr]), ?_, ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, c₅⟩)
    · rw [g₅ _ i, g₄ _ e, u₄.other _ d, u₃.other _ b, u₂.other _ a]
    · rw [g₅ _ (by decide), g₄ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h4]
    · rw [hD, g₅ _ (by decide), g₄ _ (by decide), u₄.other _ (by decide), u₃.gpr, bt₂]
    · rw [hN, g₅ _ (by decide), g₄ _ (by decide), u₄.gpr]
    · rw [g₅ _ (by decide), a₄ k hk]
    · rw [rd₅, rd₄, u₄.rd, u₃.rd, u₂.rd]
    · rw [wr₅, wr₄, u₄.wr, u₃.wr, u₂.wr]
    · rw [sp₅, sp₄, u₄.sp, u₃.sp, u₂.sp]
    · rw [m₅, m₄, u₄.mem, u₃.mem, u₂.mem]
  · have hD : c.dReg = .r2 := by unfold Core.dReg; rw [hr]; rfl
    have hN : c.nReg = .r3 := by unfold Core.nReg; rw [hr]; rfl
    have hn3 : c.arg3 = none := by
      cases h3 : c.arg3
      · rfl
      · have := S.arg3_rounds (by rw [h3]; rfl); rw [hr] at this; cases this
    simp only [↓reduceIte, List.cons_append, List.nil_append, hD, hN]
    refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_add (op2_imm enc) fun s₄ u₄ => wp_mov (op2_imm (by decide))
      fun s₅ u₅ => WP.block_append_iff.2 (arg3_wp S fun s₅' g₅' n₅ _ rd₅' wr₅' sp₅' m₅' => scrArg_wp S
      (by rw [g₅' _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), h8]) fun s₆ g₆ c₆ rd₆ wr₆ sp₆ m₆ =>
      ⟨fun x a b d e i => ?_, ?_, fun _ => ?_, ?_, ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, c₆⟩)
    · rw [g₆ _ i, g₅' _ e, u₅.other _ e, u₄.other _ d, u₃.other _ b, u₂.other _ a]
    · rw [g₆ _ (by decide), g₅' _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, h4]
    · rw [g₆ _ (by decide), g₅' _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
        u₂.other _ (by decide), h11 hr]
    · rw [hD, g₆ _ (by decide), g₅' _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), bt₂]
    · rw [hN, g₆ _ (by decide), n₅ hn3, u₅.gpr]
    · rw [hn3] at hk; cases hk
    · rw [rd₆, rd₅', u₅.rd, u₄.rd, u₃.rd, u₂.rd]
    · rw [wr₆, wr₅', u₅.wr, u₄.wr, u₃.wr, u₂.wr]
    · rw [sp₆, sp₅', u₅.sp, u₄.sp, u₃.sp, u₂.sp]
    · rw [m₆, m₅', u₅.mem, u₄.mem, u₃.mem, u₂.mem]

section
variable {c : Core} {S : CoreSpec c} {s₀ : State} (hp : UPre c S byteMode s₀)
include hp

theorem UPre.fDF : (Dp c s₀).toNat + N c s₀ ≤ 2 ^ 32 := by
  have := hp.fD; rw [ds_byteMode, Nat.mul_one] at this; exact this

theorem UPre.oA_addr : State.addr (Sc c s₀ + BitVec.ofNat 32 oOff) = oA c s₀ := by
  have := hp.fS; have := S.bs_pos
  unfold Core.scratchBytes Core.csOff at *
  exact addr_add (by omega_arith)

omit hp in
theorem UPre.o_sub_scr : Region.Sub ⟨oA c s₀, c.bs⟩ (scrR c s₀) :=
  VG.Offset.sub_base _ (by unfold Core.scratchBytes Core.csOff; omega_arith)

omit hp in
theorem UPre.o_sub_blk : Region.Sub ⟨oA c s₀, c.bs⟩ (blkR c s₀) := Region.sub_prefix (by omega_arith)

/-- The chaining block, apart from the callee's working space. -/
theorem UPre.o_cs : Region.Disjoint ⟨oA c s₀, c.bs⟩ (csR c s₀) := by
  by_cases hs : c.stackScratch = 0
  · exact fun a _ h => csR_empty hs a h
  have hS := hp.fS; unfold Core.scratchBytes at hS
  have hcs : c.csOff = oOff + 2 * c.bs := rfl
  show Region.Disjoint ⟨State.addr (Sc c s₀) + BitVec.ofNat 64 oOff, c.bs⟩ ⟨State.addr (Cs c s₀), _⟩
  rw [hp.cs_addr hs]; exact VG.Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)

omit hp in
/-- The memory on entry to the call, since entry: changed only in the data,
the scratch buffer and the stack. -/
theorem FInv.frame0 {M : Mode} {k : Nat} {s : State} (h : FInv c S M s₀ k s) :
    Frame [dataF c s₀, scrR c s₀, belowR S s₀] s₀.mem s.mem := by
  have f₀ : Frame [dataF c s₀, scrR c s₀, belowR S s₀] s₀.mem (savedMem c s₀) :=
    (UPre.savedMem_frame (c := c) (s₀ := s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR c s₀, .tail _ (.head _), UPre.slots_sub⟩
  refine f₀.trans (h.frame.sub fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, .head _, fun _ h => h⟩
  · exact ⟨scrR c s₀, .tail _ (.head _), UPre.blk_sub⟩
  · exact ⟨_, .tail _ (.tail _ (.head _)), fun _ h => h⟩

omit hp in
/-- A region apart from the scratch buffer is apart from the chaining
block. -/
theorem UPre.disj_o {R : Region} (hs : R.Disjoint (scrR c s₀)) : R.Disjoint ⟨oA c s₀, c.bs⟩ :=
  hs.sub_right UPre.o_sub_scr

/-- The call's arguments make its precondition. -/
theorem UPre.callPreO {s₂ : State} (hsp : s₂.sp = s₀.sp) (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr)
    (hsy : s₂.syms = s₀.syms) (hf : Frame [dataF c s₀, scrR c s₀, belowR S s₀] s₀.mem s₂.mem) {s : State}
    (a : ArgsA c (Kp s₀) (Rp s₀) (Sc c s₀) s s₂) :
    CallPre c S s₂ (Kp s₀) (Rp s₀) (Sc c s₀ + BitVec.ofNat 32 oOff) (Cs c s₀) := by
  have hO := hp.oA_addr
  have et : tabRegs S.consts s₂ = tabRegs S.consts s₀ := by simp only [tabRegs, hsy]
  have tw := hp.tabs.2.1
  have hS := hp.fS
  refine ⟨a.r0, a.r1, hp.rok, a.rD, a.rN, a.a3, by rw [hsp]; exact hp.stk, hp.fK, ?_, ?_, ?_, ?_, ?_, ?_,
    fun hs => by rw [a.r12 hs], hp.cs_fit, hp.key_scr.sub_right hp.cs_sub_scr, ?_,
    by rw [hsp]; exact hp.b_scr.sub_right hp.cs_sub_scr, fun hs => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : c.bs ≤ 4096 := by have := S.bw_le; omega_arith
    have := S.bs_pos
    have ho : oOff = 40 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oOff) (by unfold oOff; omega_arith),
      Nat.mod_eq_of_lt (by unfold Core.scratchBytes Core.csOff at hS; omega_arith)]
    unfold Core.scratchBytes Core.csOff at hS; omega_arith
  · rw [hO]; exact UPre.disj_o hp.key_scr
  · rw [hsp]; exact hp.b_key
  · rw [hsp, hO]; exact UPre.disj_o hp.b_scr
  · rw [hrd, hwr]; exact Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.key_in
  · rw [hwr, hO]; exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, hp.scr_in, oOff, rfl, by show oOff + c.bs ≤ c.scratchBytes; unfold Core.scratchBytes Core.csOff; omega_arith⟩
  · rw [hO]; exact hp.o_cs
  · rw [hwr]; exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      unfold Core.scratchBytes at hS
      exact ⟨_, hp.scr_in, c.csOff, hp.cs_addr hs, by show c.csOff + c.stackScratch ≤ c.scratchBytes; rfl⟩
  · rw [et, hrd]; exact fun t ht => (tw t ht).1
  · have e2 : (fun n => State.addr (s₂.syms n)) = fun n => State.addr (s₀.syms n) := by rw [hsy]
    rw [e2]
    refine held_frame hf (fun t ht r hr => ?_) (fun t ht => ?_) hp.tabs.1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (tw t ht).2.2.1 _ hp.data_in
      · exact (tw t ht).2.2.1 _ hp.scr_in
      · exact (tw t ht).2.2.2
    · have := (tw t ht).2.1; omega_arith
  · rw [et]; exact fun t ht => (tw t ht).2.1
  · rw [et, hO]; exact fun t ht => UPre.disj_o ((tw t ht).2.2.1 _ hp.scr_in)
  · rw [et]; exact fun t ht => ((tw t ht).2.2.1 _ hp.scr_in).sub_right hp.cs_sub_scr
  · rw [et, hsp]; exact fun t ht => (tw t ht).2.2.2
  · rw [et]; exact hp.tabs.2.2

end

/-! ## The partial segment -/

/-- What the byte loop works on: the `r` bytes at `R` (in `r6`, their count
in `r7`) and those at `K` (in `r0`), apart, readable and writable. -/
structure XPre (s₀ : State) (K R : BitVec 32) (r : Nat) : Prop where
  fK : K.toNat + r ≤ 2 ^ 32
  fR : R.toNat + r ≤ 2 ^ 32
  disj : Region.Disjoint ⟨State.addr K, r⟩ ⟨State.addr R, r⟩
  rdK : Covers [⟨State.addr K, r⟩] (s₀.rd ++ s₀.wr)
  wrR : Covers [⟨State.addr R, r⟩] s₀.wr

/-- The bytes at `R` XORed with those at `K`. -/
abbrev xf (m : Mem) (K R : Addr) : Nat → Byte := fun i => m (R + BitVec.ofNat 64 i) ^^^ m (K + BitVec.ofNat 64 i)

/-- The byte loop, before byte `j`. -/
structure XInv (s₀ : State) (K R : BitVec 32) (r : Nat) (j : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = K + BitVec.ofNat 32 j
  r6 : s.gpr .r6 = R + BitVec.ofNat 32 j
  r7 : s.gpr .r7 = BitVec.ofNat 32 (r - j)
  lt : j < r
  mem : s.mem = over s₀.mem (State.addr R) j (xf s₀.mem (State.addr K) (State.addr R))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  gpr : ∀ x, x ≠ .r0 → x ≠ .r6 → x ≠ .r7 → x ≠ .r9 → x ≠ .r10 → s.gpr x = s₀.gpr x

/-- The byte loop, done. -/
structure XDone (s₀ : State) (K R : BitVec 32) (r : Nat) (s : State) : Prop where
  z : s.z = true
  mem : s.mem = over s₀.mem (State.addr R) r (xf s₀.mem (State.addr K) (State.addr R))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  gpr : ∀ x, x ≠ .r0 → x ≠ .r6 → x ≠ .r7 → x ≠ .r9 → x ≠ .r10 → s.gpr x = s₀.gpr x

theorem add0_32 (p : BitVec 32) : p + BitVec.ofNat 32 0 = p := BitVec.add_zero p

theorem inRd_of {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem setWidth32_xor_byte (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).setWidth 8 = a ^^^ b := by
  rw [BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_setWidth_of_le _ (by decide),
    BitVec.setWidth_eq, BitVec.setWidth_eq]

theorem xorByte_wp {s₀ : State} {K R : BitVec 32} {r : Nat} (hp : XPre s₀ K R r) {j : Nat} {s : State}
    (hi : XInv s₀ K R r j s) :
    WP isa (.block xorByte) s fun s' =>
      (isa.eval .ne s' = some false ∧ XDone s₀ K R r s') ∨
      (isa.eval .ne s' = some true ∧ XInv s₀ K R r (j + 1) s') := by
  have hj := hi.lt
  have fK := hp.fK
  have fR := hp.fR
  have aR : State.addr (s.gpr .r6 + BitVec.ofNat 32 0) = State.addr R + BitVec.ofNat 64 j := by
    rw [hi.r6, add0_32]; exact addr_add (by omega_arith)
  have aK : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = State.addr K + BitVec.ofNat 64 j := by
    rw [hi.r0, add0_32]; exact addr_add (by omega_arith)
  have inR : InRegions s₀.wr (State.addr R + BitVec.ofNat 64 j) 1 :=
    hp.wrR _ _ ⟨_, List.mem_singleton_self _, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have inK : InRegions (s₀.rd ++ s₀.wr) (State.addr K + BitVec.ofNat 64 j) 1 :=
    hp.rdK _ _ ⟨_, List.mem_singleton_self _, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hr64 : r ≤ 2 ^ 64 := by omega_arith
  -- The bytes read, as on entry.
  have mR : s.mem (State.addr R + BitVec.ofNat 64 j) = s₀.mem (State.addr R + BitVec.ofNat 64 j) := by
    rw [hi.mem]; exact VG.Proof.Modes.over_out (by rw [VG.Proof.Modes.off_self _ (by omega_arith)]; omega_arith)
  have mK : s.mem (State.addr K + BitVec.ofNat 64 j) = s₀.mem (State.addr K + BitVec.ofNat 64 j) := by
    rw [hi.mem]
    exact VG.Proof.Modes.over_sep (hp.disj.symm.sub_left (Region.sub_prefix (by omega_arith))) hj hr64
  simp only [xorByte]
  refine wp_ldrb (a := State.addr R + BitVec.ofNat 64 j) (by decide) aR (by rw [hi.rd, hi.wr]; exact inRd_of (s := s₀) inR)
    fun s₁ u₁ => ?_
  refine wp_ldrb (a := State.addr K + BitVec.ofNat 64 j) (by decide) (by rw [u₁.other _ (by decide)]; exact aK)
    (by rw [u₁.rd, u₁.wr, hi.rd, hi.wr]; exact inK) fun s₂ u₂ => ?_
  refine VG.Proof.CmacAes.Arm.wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_strb (a := State.addr R + BitVec.ofNat 64 j) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact aR)
    (by rw [u₃.wr, u₂.wr, u₁.wr, hi.wr]; exact inR) fun s₄ u₄ => ?_
  refine wp_add (op2_imm (by decide)) fun s₅ u₅ => wp_add (op2_imm (by decide)) fun s₆ u₆ =>
    wp_subs (op2_imm (by decide)) fun s₇ u₇ z₇ => WP.block_nil ?_
  have r7 : s₇.gpr .r7 = BitVec.ofNat 32 (r - (j + 1)) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hi.r7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.Arm.sub_ofNat (by omega_arith), Nat.sub_sub]
  have z : s₇.z = decide (r - (j + 1) = 0) := by
    rw [z₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hi.r7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.Arm.sub_ofNat (by omega_arith), Nat.sub_sub]
    exact ofNat_beq_zero (by omega_arith)
  have ev : VG.Arm.eval .ne s₇ = some !decide (r - (j + 1) = 0) := by rw [eval_ne, z]
  have mem₇ : s₇.mem = over s₀.mem (State.addr R) (j + 1) (xf s₀.mem (State.addr K) (State.addr R)) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.other _ (by decide), u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, mR,
      mK, setWidth32_xor_byte, hi.mem]
    exact VG.Proof.Modes.Arm.writeW_over_step (by omega_arith)
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hi.wr]
  have sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hi.sp]
  have g₇ : ∀ x, x ≠ .r0 → x ≠ .r6 → x ≠ .r7 → x ≠ .r9 → x ≠ .r10 → s₇.gpr x = s₀.gpr x :=
    fun x a b d e f => by
      rw [u₇.other _ d, u₆.other _ b, u₅.other _ a, u₄.gpr, u₃.other _ e, u₂.other _ f, u₁.other _ e,
        hi.gpr x a b d e f]
  by_cases hdone : j + 1 = r
  · refine .inl ⟨by show VG.Arm.eval .ne s₇ = _; rw [ev, decide_eq_true (by omega_arith)]; rfl, ⟨by rw [z, decide_eq_true (by omega_arith)], by rw [mem₇, hdone], rd₇, wr₇, sp₇, g₇⟩⟩
  · refine .inr ⟨by show VG.Arm.eval .ne s₇ = _; rw [ev, decide_eq_false (by omega_arith)]; rfl, ⟨?_, ?_, r7, by omega_arith, mem₇, rd₇, wr₇, sp₇, g₇⟩⟩
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), hi.r0, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        VG.Offset.add_add]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), hi.r6, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        VG.Offset.add_add]

/-- The byte loop, from its first byte. -/
theorem xorLoop_wp {s₀ : State} {K R : BitVec 32} {r : Nat} (hp : XPre s₀ K R r) (h0 : XInv s₀ K R r 0 s₀) :
    WP isa (.loop (.block xorByte) .ne) s₀ (XDone s₀ K R r) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = r - j ∧ XInv s₀ K R r j s) (fun m s hs => ?_) r s₀
    ⟨0, by simp, h0⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (xorByte_wp hp hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, r - (j + 1), by have := d.lt; have := hj.lt; omega, j + 1, rfl, d⟩

/-- The bytes `over` leaves: those at `R` XORed with those at `K`. -/
theorem bytesAt_over_xf (m : Mem) (K R : Addr) {r L : Nat} (hr : r ≤ L) (h64 : r ≤ 2 ^ 64) :
    bytesAt (over m R r (xf m K R)) R r = Spec.Cbc.xor (bytesAt m R r) (bytesAt m K L) := by
  rw [bytesAt_over_self _ _ _ h64]
  apply List.ext_getElem (by simp [Spec.Cbc.xor, bytesAt]; omega_arith)
  intro i h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [List.getElem_map, List.getElem_range, Spec.Cbc.xor, List.getElem_zipWith, bytesAt]

/-! ## One segment -/

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S byteMode s₀)
include hp

/-- The address of segment `k`. -/
theorem UPre.dkF_addr {k : Nat} (hk : c.bs * k < N c s₀) :
    State.addr (Dp c s₀ + BitVec.ofNat 32 (c.bs * k)) = State.addr (Dp c s₀) + BitVec.ofNat 64 (c.bs * k) :=
  addr_add (by have := hp.fDF; omega_arith)

theorem UPre.dkF_toNat {k : Nat} (hk : c.bs * k < N c s₀) :
    (Dp c s₀ + BitVec.ofNat 32 (c.bs * k)).toNat = (Dp c s₀).toNat + c.bs * k := by
  have := hp.fDF
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c.bs * k) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

omit hp in
/-- `l` bytes at offset `d` of the data. -/
theorem dataF_sub {d l : Nat} (h : d + l ≤ N c s₀) :
    Region.Sub ⟨State.addr (Dp c s₀) + BitVec.ofNat 64 d, l⟩ (dataF c s₀) :=
  VG.Offset.sub_base _ (by show _ ≤ N c s₀ * c.ds byteMode; rw [ds_byteMode]; omega_arith)

/-- Block `k`'s layout, for the mode's operations. -/
theorem UPre.layF {k : Nat} (hk : c.bs * (k + 1) ≤ N c s₀) :
    Lay c c.bs (Dp c s₀ + BitVec.ofNat 32 (c.bs * k)) (Sc c s₀) s₀.wr := by
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have hb := S.bs_pos
  have hk' : c.bs * k < N c s₀ := by rw [Nat.mul_succ] at hk; omega_arith
  refine ⟨S.bw_pos, S.bw_le, hb, Nat.le_refl _, ?_, by omega_arith, ?_, ?_, ?_⟩
  · rw [hp.dkF_toNat hk']; have := hp.fDF; rw [Nat.mul_succ] at hk; omega_arith
  · exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨dataF c s₀, hp.data_in, c.bs * k, hp.dkF_addr hk', ?_⟩
      show _ ≤ N c s₀ * c.ds byteMode; rw [ds_byteMode, Nat.mul_one, Nat.mul_succ] at *; omega_arith
  · exact cov_off (R := scrR c s₀) hp.scr_in (by show oOff + 2 * c.bs ≤ c.scratchBytes; omega_arith)
  · rw [hp.dkF_addr hk']
    exact (hp.data_scr.sub_left (dataF_sub (by rw [Nat.mul_succ] at hk; omega_arith))).sub_right UPre.blk2_sub

omit hp in
theorem take_succ_xsF {k : Nat} (hk : k < nF c s₀) :
    (xsF c s₀).take (k + 1) = (xsF c s₀).take k ++ [(xsF c s₀)[k]'(by rw [length_blocksOf]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_blocksOf]; exact hk)]
  rfl

omit hp in
theorem rKF_length {k : Nat} (hk : k ≤ nF c s₀) : (rKF S s₀ M k).1.length = k := by
  rw [runSeq_length, List.length_take, length_blocksOf]; omega_arith

/-- Block `k` before the step, from the invariant. -/
theorem FInv.block {k : Nat} {s : State} (h : FInv c S M s₀ k s) (hk : k < nF c s₀) :
    bytesAt s.mem (State.addr (Dp c s₀ + BitVec.ofNat 32 (c.bs * k))) c.bs =
      (xsF c s₀)[k]'(by rw [length_blocksOf]; exact hk) := by
  have hl : (rKF S s₀ M k).1.length = k := rKF_length (S := S) (M := M) (Nat.le_of_lt hk)
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_eq_getElem (show k < (blocksOf c.bs s.mem (State.addr (Dp c s₀)) (nF c s₀)).length by
      rw [length_blocksOf]; exact hk),
    List.getElem?_append_right (show (rKF S s₀ M k).1.length ≤ k by omega_arith), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero,
    List.getElem?_eq_getElem (show k < (xsF c s₀).length by rw [length_blocksOf]; exact hk)] at this
  have hkN : c.bs * k < N c s₀ := by
    have := VG.Proof.Modes.idx_lt (L := c.bs) hk; have := nF_le c s₀; have := S.bs_pos; omega_arith
  rw [hp.dkF_addr hkN, ← getElem_blocksOf _ _ _ hk]
  exact Option.some.inj this

omit hp in
theorem stepOf_final (hM : FinalOk c M) (ciph : Spec.Cbc.Cipher) (b : Blks) :
    stepOf M ciph b = runOps M.post (b.set .o (ciph b.o)) := by
  simp only [stepOf, runOps, hM.pre, hM.tgt, List.foldl_nil]; rfl

omit hp in
/-- The loop's invariant after all the whole blocks, with no bytes after
them, is the final one. -/
theorem FInv.done {s : State} (h : FInv c S M s₀ (nF c s₀) s) (hr : rF c s₀ = 0) : FDone c S M s₀ s := by
  refine ⟨h.r5, h.r8, h.sp, h.rd, h.wr, h.frame, ?_, ?_, by rw [ite_eq_left hr]; exact h.o⟩
  · rw [h.data, List.drop_of_length_le (by rw [length_blocksOf]), List.append_nil]
  · rw [hr]; simp [bytesAt, Spec.Cbc.xor]

end

/-- What the call of segment `k` leaves, from `s`. -/
structure CallDone (c : Core) (S : CoreSpec c) (M : Mode) (s₀ : State) (k : Nat) (s s₃ : State) : Prop where
  regs : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r9 → s₃.gpr r = s.gpr r
  sp : s₃.sp = s₀.sp
  rd : s₃.rd = s₀.rd
  wr : s₃.wr = s₀.wr
  frame : Frame [⟨oA c s₀, c.bs⟩, csR c s₀, belowR S s₀] s.mem s₃.mem
  o : bytesAt s₃.mem (oA c s₀) c.bs = ciph S s₀ (rKF S s₀ M k).2.o

/-- What a segment leaves. -/
def SegPost (c : Core) (S : CoreSpec c) (M : Mode) (s₀ : State) (k : Nat) (s' : State) : Prop :=
  s'.z = decide (N c s₀ ≤ c.bs * (k + 1)) ∧ (N c s₀ ≤ c.bs * (k + 1) → FDone c S M s₀ s') ∧
    (c.bs * (k + 1) < N c s₀ → FInv c S M s₀ (k + 1) s')

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S byteMode s₀)
include hp

/-- The call of a segment, on the chaining block. -/
theorem call_seg {k : Nat} {s : State} (h : FInv c S M s₀ k s) (hsy : s.syms = s₀.syms) :
    WP isa (.block (c.callArgs .o)) s fun s₂ => WP isa c.callStep s₂ (CallDone c S M s₀ k s) := by
  refine VG.Arm.WP.mono_syms (callArgsO_wp S h.r4 h.r8 h.r11) fun s₂ a sy₂ => ?_
  have f₂ : Frame [dataF c s₀, scrR c s₀, belowR S s₀] s₀.mem s₂.mem := by rw [a.mem]; exact h.frame0
  have sp₂ : s₂.sp = s₀.sp := by rw [a.sp, h.sp]
  refine WP.mono (call_wp S (hp.callPreO sp₂ (by rw [a.rd, h.rd]) (by rw [a.wr, h.wr]) (sy₂.trans hsy) f₂ a))
    fun s₃ cp => ⟨fun r hr hl _ => ?_, by rw [cp.sp, sp₂], by rw [cp.rd, a.rd, h.rd], by rw [cp.wr, a.wr, h.wr], ?_, ?_⟩
  · rw [cp.saved r hr hl, a.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr)]
  · have fr := cp.frame
    rw [hp.oA_addr, sp₂, a.mem] at fr
    exact fr
  · rw [← hp.oA_addr, cp.out, hp.oA_addr, hp.ciph_eq f₂, a.mem, h.o]

/-- A partial segment: its bytes XORed with the chaining block's first. -/
theorem tail_seg {k : Nat} (hk : c.bs * k < N c s₀) (ht : N c s₀ - c.bs * k < c.bs) {s s₅ : State}
    (h : FInv c S M s₀ k s) (cd : CallDone c S M s₀ k s s₅)
    (r0 : s₅.gpr .r8 = Sc c s₀) (r6 : s₅.gpr .r6 = Dp c s₀ + BitVec.ofNat 32 (c.bs * k))
    (r7 : s₅.gpr .r7 = BitVec.ofNat 32 (N c s₀ - c.bs * k))
    (g5 : s₅.gpr .r5 = Ivp c s₀) :
    WP isa tailCode s₅ (SegPost c S M s₀ k) := by
  have hb := S.bs_pos
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have ho : oOff = 40 := rfl
  have hkn : nF c s₀ = k := Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega_arith)
    (by rw [Nat.mul_comm, Nat.mul_succ]; omega_arith)
  have hrF : rF c s₀ = N c s₀ - c.bs * k := by have := nF_rF c s₀; rw [hkn] at this; omega_arith
  have hr0 : 0 < rF c s₀ := by omega_arith
  have hrb : rF c s₀ < c.bs := Nat.mod_lt _ hb
  have fD := hp.fDF
  have hR := hp.dkF_addr hk
  have hO := hp.oA_addr
  have tailE : State.addr (Dp c s₀ + BitVec.ofNat 32 (c.bs * k)) = tailA c s₀ := by
    rw [hR]; show _ = State.addr (Dp c s₀) + BitVec.ofNat 64 (c.bs * nF c s₀); rw [hkn]
  simp only [tailCode]
  refine WP.seq (wp_add (op2_imm (by show encodable (BitVec.ofNat 32 40) = true; decide)) fun s₆ u₆ =>
    WP.block_nil ?_)
  have xp : XPre s₆ (Sc c s₀ + BitVec.ofNat 32 oOff) (Dp c s₀ + BitVec.ofNat 32 (c.bs * k)) (rF c s₀) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oOff) (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
    · rw [hp.dkF_toNat hk]; omega_arith
    · rw [hO, tailE]
      exact (hp.data_scr.sub_left (dataF_sub (by have := nF_rF c s₀; omega_arith))).symm.sub_left
        (fun a h => UPre.o_sub_scr a (Region.sub_prefix (by omega_arith) a h))
    · rw [u₆.rd, u₆.wr, cd.rd, cd.wr, hO]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_right _ hp.scr_in, oOff, rfl, by show oOff + rF c s₀ ≤ c.scratchBytes; omega_arith⟩
    · rw [u₆.wr, cd.wr, hR]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, hp.data_in, c.bs * k, rfl, by
          show c.bs * k + rF c s₀ ≤ N c s₀ * c.ds byteMode; rw [ds_byteMode]; omega_arith⟩
  have x0 : XInv s₆ (Sc c s₀ + BitVec.ofNat 32 oOff) (Dp c s₀ + BitVec.ofNat 32 (c.bs * k)) (rF c s₀) 0 s₆ :=
    ⟨by rw [u₆.gpr, r0, add0_32], by rw [u₆.other _ (by decide), r6, add0_32],
      by rw [u₆.other _ (by decide), r7, hrF, Nat.sub_zero], hr0, by rw [VG.Proof.Modes.over_zero], rfl, rfl, rfl,
      fun _ _ _ _ _ _ => rfl⟩
  refine WP.mono (xorLoop_wp xp x0) fun s' d => ?_
  have dmem : s'.mem = over s₆.mem (tailA c s₀) (rF c s₀) (xf s₆.mem (oA c s₀) (tailA c s₀)) := by
    rw [d.mem, hO, tailE]
  -- What the call and the byte loop changed.
  have hr64 : rF c s₀ ≤ 2 ^ 64 := by omega_arith
  have m₆ : s₆.mem = s₅.mem := u₆.mem
  have ftail : Frame [⟨tailA c s₀, rF c s₀⟩] s₅.mem s'.mem := by rw [dmem, m₆]; exact over_frame _ _ _ _
  have tailD : (⟨tailA c s₀, rF c s₀⟩ : Region).Disjoint (scrR c s₀) :=
    hp.data_scr.sub_left (dataF_sub (by have := nF_rF c s₀; omega_arith))
  have tailB : (⟨tailA c s₀, rF c s₀⟩ : Region).Disjoint (belowR S s₀) :=
    hp.b_data.symm.sub_left (dataF_sub (by have := nF_rF c s₀; omega_arith))
  have dcall : ∀ {R : Region}, R.Disjoint (scrR c s₀) → R.Disjoint (belowR S s₀) →
      ∀ r ∈ [(⟨oA c s₀, c.bs⟩ : Region), csR c s₀, belowR S s₀], R.Disjoint r := fun h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact UPre.disj_o h1
    · exact h1.sub_right hp.cs_sub_scr
    · exact h2
  have oT : (⟨oA c s₀, c.bs⟩ : Region).Disjoint ⟨tailA c s₀, rF c s₀⟩ := (UPre.disj_o tailD).symm
  refine ⟨by rw [d.z, decide_eq_true (by rw [Nat.mul_succ]; omega_arith)], fun _ => ⟨?_, ?_, by rw [d.sp, u₆.sp, cd.sp],
    by rw [d.rd, u₆.rd, cd.rd], by rw [d.wr, u₆.wr, cd.wr], ?_, ?_, ?_, ?_⟩, fun hlt => absurd hlt (by
      rw [Nat.mul_succ]; omega_arith)⟩
  · rw [d.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), u₆.other _ (by decide), g5]
  · rw [d.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), u₆.other _ (by decide), r0]
  · -- The frame.
    refine h.frame.trans ((cd.frame.sub fun r hr => ?_).trans (ftail.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, .tail _ (.head _), UPre.o_sub_blk⟩
      · exact ⟨_, .tail _ (.head _), hp.cs_sub_blk⟩
      · exact ⟨_, .tail _ (.tail _ (.head _)), fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, .head _, dataF_sub (by have := nF_rF c s₀; omega_arith)⟩
  · -- The whole blocks: as before.
    have hd := h.data
    rw [List.drop_of_length_le (by rw [length_blocksOf, hkn]), List.append_nil, ← hkn] at hd
    rw [← hd]
    refine List.map_congr_left fun j hj => ?_
    have hj := List.mem_range.mp hj
    have hjl := VG.Proof.Modes.idx_lt (L := c.bs) hj
    have hsub := dataF_sub (c := c) (s₀ := s₀) (d := c.bs * j) (l := c.bs) (by have := nF_le c s₀; omega_arith)
    rw [VG.Proof.Modes.bytesAt_frame ftail (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := nF_le c s₀; have := nF_rF c s₀
      exact VG.Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
      (by omega_arith)]
    exact VG.Proof.Modes.bytesAt_frame cd.frame (dcall (hp.data_scr.sub_left hsub)
      (hp.b_data.symm.sub_left hsub)) (by omega_arith)
  · -- The bytes after them.
    rw [dmem, m₆, bytesAt_over_xf _ _ _ (L := c.bs) (Nat.le_of_lt hrb) hr64, cd.o,
      VG.Proof.Modes.bytesAt_frame cd.frame (dcall tailD tailB) hr64, h.tail, hkn]
  · rw [ite_eq_right (Nat.pos_iff_ne_zero.mp hr0), VG.Proof.Modes.bytesAt_frame ftail (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact oT) (by omega_arith), cd.o, hkn]

/-- A whole segment: the mode's operations, and on to the next. -/
theorem whole_seg (hM : FinalOk c M) {k : Nat} (hk : c.bs * (k + 1) ≤ N c s₀) {s s₅ : State}
    (h : FInv c S M s₀ k s) (cd : CallDone c S M s₀ k s s₅) :
    WP isa (.block (c.opsCode M.post ++ c.advanceBytes)) s₅ (SegPost c S M s₀ k) := by
  have g := cd.regs
  have hb := S.bs_pos
  have hS := hp.fS
  have fD := hp.fDF
  have hk' : c.bs * k < N c s₀ := by rw [Nat.mul_succ] at hk; omega_arith
  have hsc0 : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have hkn : k < nF c s₀ := Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le hb).2 (by rw [Nat.mul_comm]; exact hk))
  have hL := hp.layF hk
  have hfit : c.bs ≤ 2 ^ 64 := by omega_arith
  have hR := hp.dkF_addr hk'
  have bsub : Region.Sub ⟨State.addr (Dp c s₀ + BitVec.ofNat 32 (c.bs * k)), c.bs⟩ (dataF c s₀) := by
    rw [hR]; exact dataF_sub (by rw [Nat.mul_succ] at hk; omega_arith)
  -- A region of the data, apart from what the call changed.
  have dcall : ∀ {R : Region}, Region.Sub R (dataF c s₀) →
      ∀ r ∈ [(⟨oA c s₀, c.bs⟩ : Region), csR c s₀, belowR S s₀], R.Disjoint r := fun hs r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact UPre.disj_o (hp.data_scr.sub_left hs)
    · exact (hp.data_scr.sub_left hs).sub_right hp.cs_sub_scr
    · exact hp.b_data.symm.sub_left hs
  let bk : Blks := (rKF S s₀ M k).2.set .d ((xsF c s₀)[k]'(by rw [length_blocksOf]; exact hkn))
  have hbm : BlkMem c c.bs (Dp c s₀ + BitVec.ofNat 32 (c.bs * k)) (Sc c s₀) s₅.mem (bk.set .o (ciph S s₀ bk.o)) := by
    intro x
    cases x
    · show bytesAt s₅.mem (State.addr (Dp c s₀ + BitVec.ofNat 32 (c.bs * k))) c.bs = _
      rw [VG.Proof.Modes.bytesAt_frame cd.frame (dcall bsub) hfit]
      exact h.block hp hkn
    · exact cd.o
    · show bytesAt s₅.mem (tA c s₀) c.bs = _
      rw [VG.Proof.Modes.bytesAt_frame cd.frame (fun r hr => ?_) hfit]
      · exact h.t
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
      rcases hr with rfl | rfl | rfl
      · exact VG.Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
      · by_cases hs : c.stackScratch = 0
        · exact fun a _ h => csR_empty hs a h
        show Region.Disjoint ⟨State.addr (Sc c s₀) + BitVec.ofNat 64 (oOff + c.bs), c.bs⟩ ⟨State.addr (Cs c s₀), _⟩
        rw [hp.cs_addr hs]; exact VG.Offset.disjoint _ (.inl (by unfold Core.csOff; omega_arith)) (by omega_arith)
          (by unfold Core.csOff; omega_arith)
      · exact (hp.b_scr.symm.sub_left (VG.Offset.sub_base _ (by omega_arith)))
  have r6 : s₅.gpr .r6 = Dp c s₀ + BitVec.ofNat 32 (c.bs * k) := by
    rw [g _ (by decide) (by decide) (by decide), h.r6]
  have r8 : s₅.gpr .r8 = Sc c s₀ := by rw [g _ (by decide) (by decide) (by decide), h.r8]
  rw [WP.block_append_iff]
  refine WP.mono (opsCode_wp (fun _ => rfl) (cd.wr ▸ hL) r6 r8 hbm hM.post) fun s₆ h₆ => ?_
  have est : runOps M.post (bk.set .o (ciph S s₀ bk.o)) = stepOf M (ciph S s₀) bk := (stepOf_final hM _ _).symm
  rw [est] at h₆
  simp only [Core.advanceBytes]
  refine wp_add (op2_imm S.bs_enc) fun s₇ u₇ => wp_subs (op2_imm S.bs_enc) fun s₈ u₈ z₈ => WP.block_nil ?_
  have r7 : s₈.gpr .r7 = BitVec.ofNat 32 (N c s₀ - c.bs * (k + 1)) := by
    rw [u₈.gpr, u₇.other _ (by decide), h₆.regs _ (by decide) (by decide), g _ (by decide) (by decide) (by decide),
      h.r7, MdStream.Arm.sub_ofNat (by rw [Nat.mul_succ] at hk; omega_arith), Nat.sub_sub, Nat.mul_succ]
  have hz : s₈.z = decide (N c s₀ ≤ c.bs * (k + 1)) := by
    rw [z₈, u₇.other _ (by decide), h₆.regs _ (by decide) (by decide), g _ (by decide) (by decide) (by decide),
      h.r7, MdStream.Arm.sub_ofNat (by rw [Nat.mul_succ] at hk; omega_arith), ofNat_beq_zero (by omega_arith)]
    exact decide_eq_decide.mpr (by rw [Nat.mul_succ]; omega_arith)
  -- What the segment changed: block `k`, the chaining and spare blocks, the callee's space and the stack.
  have fstep : Frame (blkRegions c c.bs (Dp c s₀ + BitVec.ofNat 32 (c.bs * k)) (Sc c s₀) ++ [csR c s₀, belowR S s₀])
      s.mem s₈.mem := by
    rw [u₈.mem, u₇.mem]
    refine (cd.frame.sub fun r hr => ?_).trans (h₆.frame.mono fun r hr => List.mem_append_left _ hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨State.addr (Sc c s₀) + BitVec.ofNat 64 oOff, 2 * c.bs⟩, List.mem_append_left _ (.tail _ (.head _)),
        Region.sub_prefix (by omega_arith)⟩
    · exact ⟨csR c s₀, List.mem_append_right _ (.head _), fun _ h => h⟩
    · exact ⟨belowR S s₀, List.mem_append_right _ (.tail _ (.head _)), fun _ h => h⟩
  have hl : (rKF S s₀ M k).1.length = k := rKF_length (S := S) (M := M) (Nat.le_of_lt hkn)
  have hrk : rKF S s₀ M (k + 1) = ((rKF S s₀ M k).1 ++ [(stepOf M (ciph S s₀) bk).d], stepOf M (ciph S s₀) bk) := by
    simp only [rKF]; rw [take_succ_xsF hkn, runSeq_snoc]
  have inv : FInv c S M s₀ (k + 1) s₈ := by
    refine ⟨?_, ?_, ?_, r7, ?_, fun hr => ?_, ?_, ?_, ?_, hkn, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), h₆.regs _ (by decide) (by decide),
        g _ (by decide) (by decide) (by decide), h.r4]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), h₆.regs _ (by decide) (by decide),
        g _ (by decide) (by decide) (by decide), h.r5]
    · rw [u₈.other _ (by decide), u₇.gpr, h₆.regs _ (by decide) (by decide), r6, VG.Offset.add_add, Nat.mul_succ]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), h₆.regs _ (by decide) (by decide), r8]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), h₆.regs _ (by decide) (by decide),
        g _ (by decide) (by decide) (by decide), h.r11 hr]
    · rw [u₈.sp, u₇.sp, h₆.sp, cd.sp]
    · rw [u₈.rd, u₇.rd, h₆.rd, cd.rd]
    · rw [u₈.wr, u₇.wr, h₆.wr, cd.wr]
    · exact h.frame.trans (fstep.sub fun r hr => by
        simp only [blkRegions, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, .head _, bsub⟩
        · exact ⟨blkR c s₀, .tail _ (.head _), Region.sub_prefix (by omega_arith)⟩
        · exact ⟨blkR c s₀, .tail _ (.head _), hp.cs_sub_blk⟩
        · exact ⟨belowR S s₀, .tail _ (.tail _ (.head _)), fun _ h => h⟩)
    · rw [blocksOf_set (k := k) fun j hj hjk => ?_, h.data, set_prefix _ _ _ hl (by rw [length_blocksOf]; exact hkn),
        hrk]
      · congr 2
        rw [u₈.mem, u₇.mem, ← hR]
        exact congrArg (fun z => [z]) (h₆.blks .d)
      · refine VG.Proof.Modes.bytesAt_frame fstep (fun r hr => ?_) hfit
        have hjl := VG.Proof.Modes.idx_lt (L := c.bs) hj
        have := nF_le c s₀
        have hsub := dataF_sub (c := c) (s₀ := s₀) (d := c.bs * j) (l := c.bs) (by omega_arith)
        simp only [blkRegions, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [hR]
          have hkl := VG.Proof.Modes.idx_lt (L := c.bs) hkn
          rcases Nat.lt_or_gt_of_ne hjk with hlt | hlt
          · exact VG.Offset.disjoint _ (.inl (by have := VG.Proof.Modes.idx_lt (L := c.bs) hlt; omega_arith))
              (by omega_arith) (by omega_arith)
          · exact VG.Offset.disjoint _ (.inr (by have := VG.Proof.Modes.idx_lt (L := c.bs) hlt; omega_arith))
              (by omega_arith) (by omega_arith)
        · exact (hp.data_scr.sub_left hsub).sub_right UPre.blk2_sub
        · exact (hp.data_scr.sub_left hsub).sub_right hp.cs_sub_scr
        · exact hp.b_data.symm.sub_left hsub
    · have := nF_rF c s₀
      rw [VG.Proof.Modes.bytesAt_frame fstep (fun r hr => ?_) (by omega_arith), h.tail]
      have hsub := dataF_sub (c := c) (s₀ := s₀) (d := c.bs * nF c s₀) (l := rF c s₀) (by omega_arith)
      simp only [blkRegions, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hR]
        have hkl := VG.Proof.Modes.idx_lt (L := c.bs) hkn
        exact VG.Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
      · exact (hp.data_scr.sub_left hsub).sub_right UPre.blk2_sub
      · exact (hp.data_scr.sub_left hsub).sub_right hp.cs_sub_scr
      · exact hp.b_data.symm.sub_left hsub
    · rw [hrk, u₈.mem, u₇.mem]; exact h₆.blks .o
    · rw [hrk, u₈.mem, u₇.mem]; exact h₆.blks .t
  refine ⟨hz, fun hle => ?_, fun _ => inv⟩
  have e : k + 1 = nF c s₀ := by
    have := VG.Proof.Modes.idx_lt (L := c.bs) hkn; have := nF_le c s₀
    exact Nat.le_antisymm hkn (by
      have h2 : c.bs * nF c s₀ ≤ c.bs * (k + 1) := by omega_arith
      exact Nat.le_of_mul_le_mul_left h2 hb)
  have hr0 : rF c s₀ = 0 := by have := nF_rF c s₀; rw [← e] at this; omega_arith
  rw [e] at inv
  exact inv.done hr0

/-- After the call: a partial segment or a whole one. -/
theorem rest_ok (hM : FinalOk c M) {k : Nat} (hk : c.bs * k < N c s₀) {s s₃ : State} (h : FInv c S M s₀ k s)
    (cd : CallDone c S M s₀ k s s₃) : WP isa (c.segRest M) s₃ (SegPost c S M s₀ k) := by
  have hb := S.bs_pos
  simp only [Core.segRest]
  refine WP.seq ?_
  simp only [Core.segTest]
  refine wp_mov (op2_lsr ⟨hM.lg1, hM.lg31⟩) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_
  have g : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r9 → s₅.gpr r = s.gpr r := fun r hr hl h9 => by
    rw [f₅.gpr, u₄.other _ h9, cd.regs r hr hl h9]
  have r7₃ : s₃.gpr .r7 = BitVec.ofNat 32 (N c s₀ - c.bs * k) := by
    rw [cd.regs _ (by decide) (by decide) (by decide), h.r7]
  have hz : s₅.z = decide (N c s₀ - c.bs * k < c.bs) := by
    rw [z₅, u₄.gpr, r7₃, ofNat_shr (by have := N_lt c s₀; omega_arith), hM.lg, cmp0 (by
      have := N_lt c s₀; have := Nat.div_le_self (N c s₀ - c.bs * k) c.bs; omega_arith)]
    exact decide_eq_decide.mpr (Nat.div_eq_zero_iff_lt hb)
  have cd₅ : CallDone c S M s₀ k s s₅ := ⟨g, by rw [f₅.sp, u₄.sp, cd.sp], by rw [f₅.rd, u₄.rd, cd.rd],
    by rw [f₅.wr, u₄.wr, cd.wr], by rw [f₅.mem, u₄.mem]; exact cd.frame, by rw [f₅.mem, u₄.mem]; exact cd.o⟩
  refine WP.ite (decide (N c s₀ - c.bs * k < c.bs)) (by show VG.Arm.eval .eq s₅ = _; rw [eval_eq, hz])
    (fun ht => ?_) (fun hf => ?_)
  · exact tail_seg hp hk (of_decide_eq_true ht) h cd₅ (by rw [g _ (by decide) (by decide) (by decide), h.r8])
      (by rw [g _ (by decide) (by decide) (by decide), h.r6]) (by rw [g _ (by decide) (by decide) (by decide), h.r7])
      (by rw [g _ (by decide) (by decide) (by decide), h.r5])
  · exact whole_seg hp hM (by have := of_decide_eq_false hf; rw [Nat.mul_succ]; omega_arith) h cd₅

/-- One segment. -/
theorem seg_ok (hM : FinalOk c M) {k : Nat} (hk : c.bs * k < N c s₀) {s : State} (h : FInv c S M s₀ k s)
    (hsy : s.syms = s₀.syms) : WP isa (c.seg M) s (SegPost c S M s₀ k) :=
  WP.seq (WP.mono (call_seg hp h hsy) fun _ h₂ => WP.seq (WP.mono h₂ fun _ cd => rest_ok hp hM hk h cd))

theorem loopF_ok (hM : FinalOk c M) {k : Nat} (hk : c.bs * k < N c s₀) {s : State} (h : FInv c S M s₀ k s)
    (hsy : s.syms = s₀.syms) : WP isa (.loop (c.seg M) .ne) s (FDone c S M s₀) := by
  have hb := S.bs_pos
  refine WP.loop (M := isa) (body := c.seg M) (c := .ne) (Q := FDone c S M s₀)
    (fun (n : Nat) (t : State) => ∃ j, n = N c s₀ - c.bs * j ∧ c.bs * j < N c s₀ ∧ FInv c S M s₀ j t ∧
      t.syms = s₀.syms) ?_ (N c s₀ - c.bs * k) s ⟨k, rfl, hk, h, hsy⟩
  rintro n t ⟨j, rfl, hj, ht, tsy⟩
  refine VG.Arm.WP.mono_syms (seg_ok hp hM hj ht tsy) fun s' ⟨hz, hd, hi⟩ sy' => ?_
  have ev : isa.eval .ne s' = some !decide (N c s₀ ≤ c.bs * (j + 1)) := by
    show VG.Arm.eval .ne s' = _; rw [eval_ne, hz]
  by_cases hle : N c s₀ ≤ c.bs * (j + 1)
  · exact .inl ⟨by rw [ev]; simp [hle], hd hle⟩
  · refine .inr ⟨by rw [ev]; simp [hle], N c s₀ - c.bs * (j + 1), by rw [Nat.mul_succ] at hle ⊢; omega_arith, j + 1,
      rfl, by omega_arith, hi (by omega_arith), sy'.trans tsy⟩

theorem midF_wp (hM : FinalOk c M) {s₁ : State} (h : FInv c S M s₀ 0 s₁) (hz : s₁.z = decide (N c s₀ = 0))
    (hsy : s₁.syms = s₀.syms) :
    WP isa (.ite .eq (.block []) (.loop (c.seg M) .ne)) s₁ (FDone c S M s₀) := by
  have ev : isa.eval .eq s₁ = some (decide (N c s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]
  by_cases hn : N c s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    have e0 : nF c s₀ = 0 := by simp only [nF, hn, Nat.zero_div]
    have r0 : rF c s₀ = 0 := by simp only [rF, hn, Nat.zero_mod]
    have h' : FInv c S M s₀ (nF c s₀) s₁ := by rw [e0]; exact h
    exact h'.done r0
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loopF_ok hp hM (by rw [Nat.mul_zero]; omega_arith) h hsy

/-! ## The epilogue -/

/-- What the epilogue starts from: the chaining block copied to the IV. -/
structure FEnd (c : Core) (S : CoreSpec c) (M : Mode) (s₀ : State) (s : State) : Prop where
  r8 : s.gpr .r8 = Sc c s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataF c s₀, blkR c s₀, belowR S s₀, ivR c s₀] (savedMem c s₀) s.mem
  data : blocksOf c.bs s.mem (State.addr (Dp c s₀)) (nF c s₀) = (rKF S s₀ M (nF c s₀)).1
  tail : bytesAt s.mem (tailA c s₀) (rF c s₀) =
    Spec.Cbc.xor (bytesAt s₀.mem (tailA c s₀) (rF c s₀)) (ciph S s₀ (rKF S s₀ M (nF c s₀)).2.o)
  iv : bytesAt s.mem (State.addr (Ivp c s₀)) c.bs =
    if rF c s₀ = 0 then (rKF S s₀ M (nF c s₀)).2.o else ciph S s₀ (rKF S s₀ M (nF c s₀)).2.o

theorem finishF_wp (hM : FinalOk c M) {s : State} (h : FDone c S M s₀ s) :
    WP isa (.block (c.finish M)) s (FEnd c S M s₀) := by
  have hfit : c.bs ≤ 2 ^ 64 := by have := hp.fS; unfold Core.scratchBytes Core.csOff at this; omega_arith
  have fr4 : Frame [dataF c s₀, blkR c s₀, belowR S s₀, ivR c s₀] (savedMem c s₀) s.mem :=
    h.frame.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h]
  unfold Core.finish
  rw [ite_eq_left hM.fin]
  have hS := hp.fS
  have hI := hp.fIv
  have fD := hp.fDF
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have hbs : c.bs = 4 * c.bw := rfl
  have hb := S.bw_le
  have ho : oOff = 40 := rfl
  have np : NPre c.bw s .r5 .r8 0 oOff (State.addr (Ivp c s₀) + BitVec.ofNat 64 0) (oA c s₀) := by
    refine ⟨by rw [h.r5], by rw [h.r8], by rw [h.r5]; omega_arith, by rw [h.r8]; omega_arith, by omega_arith,
      by omega_arith, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
    · rw [h.wr]; exact cov_off (R := ivR c s₀) (hp.fin rfl) (by show 0 + 4 * c.bw ≤ c.bs; omega_arith)
    · rw [h.rd, h.wr]
      exact cov_off (R := scrR c s₀) (List.mem_append_right _ hp.scr_in)
        (by show oOff + 4 * c.bw ≤ c.scratchBytes; omega_arith)
    · exact (hp.iv_scr.sub_left (VG.Offset.sub_base _ (by omega_arith))).sub_right
        (VG.Offset.sub_base _ (by omega_arith))
  -- The data's bytes are apart from the IV.
  have ivD : ∀ {d l : Nat}, d + l ≤ N c s₀ →
      Region.Disjoint ⟨State.addr (Ivp c s₀) + BitVec.ofNat 64 0, 4 * c.bw⟩
        ⟨State.addr (Dp c s₀) + BitVec.ofNat 64 d, l⟩ := fun hdl => by
    rw [add0]; exact (hp.iv_data.sub_left (Region.sub_prefix (by omega_arith))).sub_right (dataF_sub hdl)
  refine WP.mono (copyN_wp np) fun s' hi => ⟨by rw [hi.regs _ (by decide) (by decide), h.r8],
    by rw [hi.sp, h.sp], by rw [hi.rd, h.rd], by rw [hi.wr, h.wr], ?_, ?_, ?_, ?_⟩
  · rw [hi.mem]
    exact fr4.trans ((VG.Proof.Modes.over_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨ivR c s₀, .tail _ (.tail _ (.tail _ (.head _))), by rw [add0]; exact Region.sub_prefix (by omega_arith)⟩)
  · rw [hi.mem, ← h.data]
    refine List.map_congr_left fun j hj => ?_
    have hj := List.mem_range.mp hj
    have := VG.Proof.Modes.idx_lt (L := c.bs) hj; have := nF_le c s₀
    exact bytesAt_over_other _ _ (ivD (by omega_arith)) (by omega_arith)
  · have := nF_rF c s₀
    rw [hi.mem, ← h.tail]
    exact bytesAt_over_other _ _ (ivD (by omega_arith)) (by omega_arith)
  · rw [hi.mem, ← h.o, add0]
    have e := bytesAt_over_self s.mem (State.addr (Ivp c s₀) + BitVec.ofNat 64 0)
      (fun i => s.mem (oA c s₀ + BitVec.ofNat 64 i)) (n := 4 * c.bw) (by omega_arith)
    rw [add0] at e
    rw [hbs, e]; rfl

theorem epilogueF_wp {s : State} (h : FEnd c S M s₀ s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ (seqFinalArm c S M).post s₀ s' := by
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have ho : oOff = 40 := rfl
  have hsv : Spill.Saved s.mem (State.addr (Sc c s₀)) s₀.gpr saved :=
    (Spill.saveMem_saved (State.addr (Sc c s₀)) s₀.gpr s₀.mem saved saved_slots).frame saved_slots h.frame
      (fun r hr => hp.slots_disj r hr)
  have hin : ∀ d, d + 4 ≤ 36 → InRegions (s.rd ++ s.wr) (State.addr (Sc c s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [h.rd, h.wr]
      exact ⟨scrR c s₀, List.mem_append_right _ hp.scr_in, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have tk : (xsF c s₀).take (nF c s₀) = xsF c s₀ := List.take_of_length_le (by rw [length_blocksOf])
  rw [show (restore : List Instr) = savedA.map (fun p => Instr.ldr p.1 .r8 p.2) ++ [.ldr .r8 .r8 16] from rfl]
  refine Spill.restore_slots_ok savedA_slots savedA_restorable (g := s₀.gpr) (by rw [h.r8]; omega_arith)
    (fun d _ hd => by rw [h.r8]; exact hin d hd)
    (by rw [h.r8]; exact fun p hp' => hsv p (by rw [saved_eq]; exact List.mem_append_left _ hp'))
    fun s₁ ld ho' m₁ rd₁ wr₁ sp₁ => ?_
  refine wp_ldr (a := State.addr (Sc c s₀) + BitVec.ofNat 64 16) (by decide)
    (by rw [ho' _ (by decide), h.r8]; exact addr_add (by omega_arith))
    (by rw [rd₁, wr₁]; exact hin 16 (by decide)) fun s₂ u₂ => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_, ?_⟩
  · by_cases h8 : r = .r8
    · subst h8; rw [u₂.gpr, m₁]; exact hsv (.r8, 16) (by decide)
    · rw [u₂.other _ h8]
      have : r ∈ savedA.map Prod.fst := by
        revert hr h8; revert r; decide
      exact Spill.restored_reg ld this
  · rw [u₂.sp, sp₁, h.sp]
  · show blocksOf c.bs s₂.mem (State.addr (Dp c s₀)) (nF c s₀) = _
    rw [u₂.mem, m₁, h.data]; simp only [rKF, tk]
  · show bytesAt s₂.mem (tailA c s₀) (rF c s₀) = _
    rw [u₂.mem, m₁, h.tail]; simp only [rKF, tk]
  · show bytesAt s₂.mem (State.addr (Ivp c s₀)) c.bs = _
    rw [u₂.mem, m₁, h.iv]; simp only [rKF, tk]

end

/-- The whole function meets its contract, for any core and mode the final
function runs. -/
theorem seqFinal_wp {c : Core} (S : CoreSpec c) {M : Mode} (hM : FinalOk c M) {s₀ : State}
    (h0 : (seqFinalArm c S M).pre s₀) :
    WP isa (c.seqFinal M) s₀ fun s' => abiPreserved s₀ s' ∧ (seqFinalArm c S M).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (VG.Arm.WP.mono_syms (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ hsy =>
    WP.seq (WP.mono (midF_wp hp hM (FInv.of_linv (M := M) h₁) hz hsy) fun _ h₂ => by
      rw [WP.block_append_iff]
      exact WP.mono (finishF_wp hp hM h₂) fun _ h₃ => epilogueF_wp hp h₃))

/-! ## CFB -/

theorem runSeq_cfbDecF (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs : List (List Byte)),
      (runSeq cfbDecF ciph b xs).1 = Spec.Cfb.decrypt ciph b.o xs ∧
        (runSeq cfbDecF ciph b xs).2.o = Spec.Cbc.next b.o xs
  | _, [] => ⟨rfl, rfl⟩
  | b, x :: xs => by
    have ih := runSeq_cfbDecF ciph (stepOf cfbDecF ciph (b.set .d x)) xs
    have hd : (stepOf cfbDecF ciph (b.set .d x)).d = Spec.Cbc.xor x (ciph b.o) := by
      simp [stepOf, runOps, runOp, cfbDecF, Blks.set, Blks.get]
    have ho : (stepOf cfbDecF ciph (b.set .d x)).o = x := by
      simp [stepOf, runOps, runOp, cfbDecF, Blks.set, Blks.get]
    rw [ho] at ih
    refine ⟨?_, ?_⟩
    · simp only [runSeq, ih.1, hd, Spec.Cfb.decrypt]
    · simp only [runSeq, ih.2, Spec.Cbc.next, List.getLastD_cons]

/-- The final function with `cfbEnc` encrypts as `Spec.Cfb.EncryptFinal` says. -/
theorem cfbEncFinal_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqFinalArm c S cfbEnc).post s s') :
    Spec.Cfb.EncryptFinal (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)) c.bs s.mem s'.mem
      (State.addr (ivArg c s)) (State.addr (dArg c s)) (nArg c s).toNat := by
  obtain ⟨h1, h2, h3⟩ := h
  have e := runSeq_cfbEnc (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)) ⟨[], bytesAt s.mem
    (State.addr (ivArg c s)) c.bs, bytesAt s.mem (State.addr (scArg c s) + BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
    (blocksOf c.bs s.mem (State.addr (dArg c s)) ((nArg c s).toNat / c.bs))
  rw [e.1] at h1
  rw [e.2] at h2 h3
  exact ⟨VG.Proof.Modes.cfbEncFinal_of _ s.mem s'.mem _ _ _ h1 h2,
    h3.trans (VG.Proof.Modes.cfbEncFinalNext_of _ _ _ _ _)⟩

/-- The final function with `cfbDecF` decrypts as `Spec.Cfb.DecryptFinal` says. -/
theorem cfbDecFinal_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqFinalArm c S cfbDecF).post s s') :
    Spec.Cfb.DecryptFinal (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)) c.bs s.mem s'.mem
      (State.addr (ivArg c s)) (State.addr (dArg c s)) (nArg c s).toNat := by
  obtain ⟨h1, h2, h3⟩ := h
  have e := runSeq_cfbDecF (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)) ⟨[], bytesAt s.mem
    (State.addr (ivArg c s)) c.bs, bytesAt s.mem (State.addr (scArg c s) + BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
    (blocksOf c.bs s.mem (State.addr (dArg c s)) ((nArg c s).toNat / c.bs))
  rw [e.1] at h1
  rw [e.2] at h2 h3
  exact ⟨VG.Proof.Modes.cfbDecFinal_of _ s.mem s'.mem _ _ _ h1 h2,
    h3.trans (VG.Proof.Modes.cfbDecFinalNext_of _ _ _ _ _)⟩

theorem cfbEnc_finalOk (c : Core) (h1 : 1 ≤ c.lg) (h31 : c.lg ≤ 31) (hl : 2 ^ c.lg = c.bs) : FinalOk c cfbEnc :=
  ⟨rfl, rfl, rfl, rfl, rfl, hl, h1, h31⟩

theorem cfbDecF_finalOk (c : Core) (h1 : 1 ≤ c.lg) (h31 : c.lg ≤ 31) (hl : 2 ^ c.lg = c.bs) : FinalOk c cfbDecF :=
  ⟨rfl, rfl, rfl, rfl, rfl, hl, h1, h31⟩

/-! ## OFB -/

/-- The final function with `ofb` encrypts and decrypts as
`Spec.Ofb.CryptFinal` says, for a cipher whose every output is a block. -/
theorem ofbFinal_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqFinalArm c S ofb).post s s')
    (hc : ∀ b, (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1) b).length = c.bs) :
    Spec.Ofb.CryptFinal (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)) c.bs s.mem s'.mem
      (State.addr (ivArg c s)) (State.addr (dArg c s)) (nArg c s).toNat := by
  obtain ⟨h1, h2, h3⟩ := h
  have hL : 0 < c.bs := Nat.mul_pos (by decide) S.bw_pos
  have e := runSeq_ofb (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)) ⟨[], bytesAt s.mem
    (State.addr (ivArg c s)) c.bs, bytesAt s.mem (State.addr (scArg c s) + BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
    (blocksOf c.bs s.mem (State.addr (dArg c s)) ((nArg c s).toNat / c.bs))
  rw [length_blocksOf] at e
  rw [e.1] at h1
  rw [e.2] at h2 h3
  refine ⟨ofbFinal_of hL hc s.mem s'.mem _ _ _ h1 h2, h3.trans ?_⟩
  rw [VG.Proof.Modes.blockCount_eq hL]
  split
  · rfl
  · exact (VG.Proof.AesOfb.next_succ _ _ _).symm

theorem ofb_finalOk (c : Core) (h1 : 1 ≤ c.lg) (h31 : c.lg ≤ 31) (hl : 2 ^ c.lg = c.bs) : FinalOk c ofb :=
  ⟨rfl, rfl, rfl, rfl, rfl, hl, h1, h31⟩

end VG.Proof.Modes.Arm

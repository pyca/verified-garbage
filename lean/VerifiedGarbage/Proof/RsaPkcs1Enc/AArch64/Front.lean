module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Front
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecMain
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecOut
public import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Front
meta import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecMain
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecOut
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Reduce
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract

/-!
# `vg_rsa_pkcs1_decrypt_precomputed` on AArch64

`Front.code` (`Impl/RsaPkcs1Enc/AArch64/Front.lean`) against
`Spec.RsaPkcs1Enc.decryptPrecomputedContract` with 3776 bytes of stack
(`front_verified`), for any callee verified against
`Proof.RsaPkcs1Enc.decryptPrecomputedBodyContract` with 3488: its proof is used
only through that contract. Both contracts have the same precondition and
public data; `FPre` names what the function uses of it.

**The call.** The stack is the callee's 3488 bytes from `B s = sp - 3776`,
the inner frame of 272 bytes from `F s = B s + 3488`, and the word saving
`x30`. `setup` copies our 17 stack arguments to the frame's bottom and
`out`, `n_len` and `msg_len` to its slots (`Ready`, by `moves_ok`), and
leaves `x0`–`x7` as they came; the callee's entry, with our read-only
buffers and the copies readable and our writable buffers writable
(`cEntry`), meets its precondition (`call_pre`): its buffers are ours, its
stack is the bottom of ours, and our writes in the frame leave the buffers'
bytes as they were (`bytes_eq`, `words_eq`). Its postcondition
(`WP.callFV`) says what it wrote at `out` and `msg_len` (`Called`).

**After the call.** In RSAES-OAEP's frame and layout of `scratch` (`Lay`,
`Rep`, `Proof/RsaOaep/AArch64/`), with the slots `sScr`, `sOut`, `sK`,
`sMl` and `sR` (`Mid`): the buffer's first `zK = 16 w` bytes cleared,
`w = ⌈k / 8⌉` (`clear_ok`, by RSAES-OAEP's `clearLoop_ok`), `out` copied to
it (`copyLoop_ok`), shifted by `k - L` in `log2 k + 1` passes over `w` words
each (`passesK_ok`), which leaves the message and zeros (`shift_val`), and
copied back (`coutLoop_ok`): `St0` … `St4`, `Fin`.
`front_ok` puts these in the frames.

**Constant time.** Two runs from states with the same public data (`Rel`):
the blocks by the taint analysis from `sp` (`setup`, `after`, `ret`) or
from the registers each piece's head sets to public values (`rel_seq_tr`,
the pins), the call by the callee's constant time, its public data being
ours (`call_pub`), and what each piece leaves by its correctness
(`rel_step`).
-/

-- separate module: the function's proofs, which build alongside `Callees.lean`, which `FrontScrub.lean` needs

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Front

open VG VG.AArch64
open VG.Impl.RsaOaep.AArch64 (frameBytes sOut sK sMl sR sScr oBuf oRsa scr mvArg mov copyLoop passBody arg)
open VG.Proof.RsaOaep.AArch64 (off off_off word Lay Rep Geo Step)

/-! ## The contracts, by name -/

/-- `vg_rsa_pkcs1_decrypt_precomputed_body`'s contract, the callee's. -/
abbrev DK (n : Nat) : Contract isa := Proof.RsaPkcs1Enc.decryptPrecomputedBodyContract AArch64.abi n

/-- `vg_rsa_pkcs1_decrypt_precomputed`'s. -/
abbrev FK (n : Nat) : Contract isa := Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi n

theorem stackArgs17 (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

/-- `out`, `*msg_len`, `scratch`, our stack arguments and our stack. -/
abbrev outR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev mlR (s : State) : Region := ⟨s.gpr .x2, 8⟩
abbrev scrR (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
abbrev argsR (s : State) : Region := ⟨stackArgAddr s 0, 136⟩
abbrev stkR (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 3776, 3776⟩

/-- `k`, `n_len`. -/
abbrev kOf (s : State) : Nat := (s.gpr .x4).toNat

/-- The read-only buffers. -/
def ro (s : State) : List Region :=
  [⟨s.gpr .x3, (s.gpr .x4).toNat⟩, ⟨s.gpr .x5, (s.gpr .x6).toNat⟩, ⟨s.gpr .x7, (stackArg s 0).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
    ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
    ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩,
    ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩]

/-- What the function uses of its precondition. -/
structure FPre (s : State) : Prop where
  sp1 : 3776 ≤ s.sp.toNat
  sp2 : s.sp.toNat + 136 ≤ 2 ^ 64
  wr : s.wr = [outR s, mlR s, scrR s]
  dOM : (outR s).Disjoint (mlR s)
  dOS : (outR s).Disjoint (scrR s)
  dMS : (mlR s).Disjoint (scrR s)
  dOA : (outR s).Disjoint (argsR s)
  dMA : (mlR s).Disjoint (argsR s)
  dSA : (scrR s).Disjoint (argsR s)
  kO : (stkR s).Disjoint (outR s)
  kM : (stkR s).Disjoint (mlR s)
  kS : (stkR s).Disjoint (scrR s)
  bO : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  bM : (s.gpr .x2).toNat + 8 ≤ 2 ^ 64
  bS : (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64
  kv : Spec.Rsa.lenValid (kOf s)
  olk : (s.gpr .x1).toNat = kOf s
  slk : Spec.Rsa.scratchWords (kOf s) ≤ (stackArg s 14).toNat
  rd : s.rd = ro s ++ [argsR s]
  kN : (stkR s).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  kE : (stkR s).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  kPr : (stkR s).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  bN : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  bE : (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64
  bPr : (stackArg s 15).toNat + (stackArg s 16).toNat * 8 ≤ 2 ^ 64
  prl : (stackArg s 16).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .x4).toNat (stackArg s 4).toNat (stackArg s 6).toNat

theorem fpre_of {s : State} (h : (FK 3776).pre s) : FPre s := by
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    AArch64.abi, AArch64.argRegs, stackArgs17, List.append_eq,
    _root_.List.range, _root_.List.range.loop] at h
  sig_split h
  rename_i sp1 sp2 rd wr oM oN oE oD oI oP oQ oDP oDQ oQI oS oPr oA mN mE mD mI mP mQ mDP mDQ mQI mS mPr mA
    nS eS dS iS pS qS dpS dqS qiS sPr sA kO kM kN kE kD kI kP kQ kDP kDQ kQI kS kPr kA bO bM bN bE bD bI bP bQ
    bDP bDQ bQI bS bPr kv olk ilk el1 elk dl1 dlk pl1 plk ql1 qlk dpl qil dql slk prl
  exact ⟨sp1, sp2, wr, oM, oS, mS, oA, mA, sA, kO, kM, kS, bO, bM, bS, kv, olk, slk, by rw [rd]; rfl, kN, kE, kPr,
    bN, bE, bPr, prl⟩

/-! ## The frames -/

/-- The bottom of our stack, `B s`; the inner frame's base `F s`, `sp` in
the body, is `B s + 3488`, above the callee's 3488 bytes. -/
abbrev B (s : State) : Addr := s.sp - BitVec.ofNat 64 3776
abbrev F (s : State) : Addr := s.sp - BitVec.ofNat 64 288

theorem F_B (s : State) : F s = B s + BitVec.ofNat 64 3488 := Offset.sub_ofNat_eq _ (by decide)

theorem sp_B (s : State) : s.sp = B s + BitVec.ofNat 64 3776 := (BitVec.sub_add_cancel _ _).symm

theorem B_toNat {s : State} (hp : FPre s) : (B s).toNat + 3776 = s.sp.toNat := by
  have := hp.sp1
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat]
  omega_arith

/-- `F s + d`, as an offset of `B s`. -/
theorem F_off (s : State) (d : Nat) : F s + BitVec.ofNat 64 d = B s + BitVec.ofNat 64 (3488 + d) := by
  rw [F_B, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- Our stack argument `j`, from `sp` in the body. -/
theorem arg_addr (s : State) (j : Nat) : F s + BitVec.ofNat 64 (arg j) = stackArgAddr s j := by
  rw [F_off, stackArgAddr, sp_B, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2; unfold arg frameBytes; omega_arith

/-- Bytes of our stack. -/
theorem stk_sub (s : State) {d n : Nat} (h : d + n ≤ 3776) : Region.Sub ⟨B s + BitVec.ofNat 64 d, n⟩ (stkR s) :=
  Offset.sub_base _ h

theorem fr_stk (s : State) {d n : Nat} (h : d + n ≤ 272) : Region.Sub ⟨F s + BitVec.ofNat 64 d, n⟩ (stkR s) := by
  rw [F_off]; exact stk_sub s (by omega_arith)

/-- The state in which the body starts. -/
abbrev entered (s : State) : State := allocated frameBytes (pushed .x30 s)

theorem entered_sp (s : State) : (entered s).sp = F s := by
  show s.sp - 16 - BitVec.ofNat 64 272 = s.sp - BitVec.ofNat 64 288
  rw [BitVec.sub_sub]; rfl

theorem lr_addr (s : State) : s.sp - 16 = B s + BitVec.ofNat 64 3760 := Offset.sub_ofNat_eq s.sp (by decide)

theorem entered_wr (s : State) : (entered s).wr = ⟨F s, frameBytes⟩ :: ⟨s.sp - 16, 16⟩ :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 272, 272⟩ : Region) :: _ = _
  rw [show s.sp - 16 - BitVec.ofNat 64 272 = F s from entered_sp s]; rfl

theorem entered_mem (s : State) : (entered s).mem = s.mem.write (s.sp - 16) 8 (s.gpr .x30) := rfl

/-! ## The setup -/

theorem exec_strX {s : State} {t n : Reg} {d : Nat} (ho : d % 8 = 0 ∧ d < 32768)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 d) 8) :
    exec (.str .x t n d) s = some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 d) (s.gpr t) } := by
  simp only [reduceExec, addr, Size.bytes, ho, and_self, ite_true, Option.bind_some,
    State.store, h, State.read, BitVec.setWidth_eq, Mem.writeW]

/-- After the first `n` moves of the stack arguments, from `u`. -/
structure Moved (u u' : State) (n : Nat) : Prop where
  rd : u'.rd = u.rd
  wr : u'.wr = u.wr
  sp : u'.sp = u.sp
  v : u'.v = u.v
  dit : u'.dit = u.dit
  gpr : ∀ r, r ≠ .x10 → u'.gpr r = u.gpr r
  fr : Frame [⟨u.sp, 136⟩] u.mem u'.mem
  args : ∀ j < n, u'.mem.readW (u.sp + BitVec.ofNat 64 (8 * j)) 64 =
    u.mem.readW (u.sp + BitVec.ofNat 64 (arg j)) 64

theorem moves_ok {u : State} (n : Nat) (hn : n ≤ 17) (h9 : u.gpr .x9 = u.sp)
    (hw : ∀ j < 17, InRegions u.wr (u.sp + BitVec.ofNat 64 (8 * j)) 8)
    (hr : ∀ j < 17, InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (arg j)) 8) :
    WP isa (.block ((List.range n).flatMap fun j => mvArg j (8 * j))) u (Moved u · n) := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, fun _ h => absurd h (by omega_arith)⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff, List.flatMap_singleton]
    refine WP.mono (ih (by omega_arith)) fun u' hm => ?_
    obtain ha : arg n % 8 = 0 ∧ arg n < 32768 := by unfold arg frameBytes; omega_arith
    obtain hd : 8 * n % 8 = 0 ∧ 8 * n < 32768 := by omega_arith
    obtain hsrc : u'.mem.readW (u.sp + BitVec.ofNat 64 (arg n)) 64 = u.mem.readW (u.sp + BitVec.ofNat 64 (arg n)) 64 :=
      hm.fr.readW (r := ⟨u.sp + BitVec.ofNat 64 (arg n), 8⟩) (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint_base _ (by unfold arg frameBytes; omega_arith) (by unfold arg frameBytes; omega_arith))
        (by decide)
    apply WP.of_runBlock
    rw [mvArg, runBlock_cons, VG.AArch64.Bytes.exec_ldrSp ha (by rw [hm.sp, hm.rd, hm.wr]; exact hr n (by omega_arith)),
      runStep_some, runBlock_cons,
      exec_strX hd (by
        rw [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ _ (by decide), hm.gpr .x9 (by decide), h9, hm.wr]
        exact hw n (by omega_arith)),
      runStep_some, runBlock_nil]
    refine ⟨_, rfl, hm.rd, hm.wr, hm.sp, hm.v, hm.dit, fun r hr => ?_, ?_, fun j hj => ?_⟩
    · exact (RegUpd.gpr_write_of_ne _ _ _ hr).trans (hm.gpr r hr)
    · show Frame _ u.mem (Mem.writeW _ _ _)
      refine hm.fr.writeW (List.mem_singleton_self _) _ ?_
      rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), hm.gpr .x9 (by decide), h9]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · show (Mem.writeW _ _ _).readW _ 64 = _
      rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), hm.gpr .x9 (by decide), h9, RegUpd.gpr_write_self,
        BitVec.setWidth_eq, hm.sp]
      by_cases hjn : j = n
      · subst hjn; rw [Mem.readW_writeW_self64, hsrc]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
        exact hm.args j (by omega_arith)

theorem arg_in (s : State) {j : Nat} (hj : j < 17) : (argsR s).Contains (stackArgAddr s j) 8 := by
  show (⟨s.sp + BitVec.ofNat 64 (8 * 0), 136⟩ : Region).Contains (s.sp + BitVec.ofNat 64 (8 * j)) 8
  rw [Nat.mul_zero, BitVec.add_zero]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem rdW (m : Mem) (a : Addr) : m.readW a 64 = m.read a 8 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

theorem argA (s : State) (j : Nat) : stackArgAddr s j = B s + BitVec.ofNat 64 (3776 + 8 * j) := by
  rw [stackArgAddr, sp_B, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- After `setup`: the stack arguments copied to the frame's bottom, and
`out`, `k`, `msg_len` in their slots. -/
structure Ready (s w : State) : Prop where
  sp : w.sp = F s
  rd : w.rd = s.rd
  wr : w.wr = (entered s).wr
  v : w.v = s.v
  dit : w.dit = s.dit
  gpr : ∀ r, r ≠ .x9 → r ≠ .x10 → w.gpr r = s.gpr r
  fr : Frame [stkR s] s.mem w.mem
  args : ∀ j < 17, w.mem.readW (F s + BitVec.ofNat 64 (8 * j)) 64 = stackArg s j
  wOut : word w.mem (F s) sOut = s.gpr .x0
  wK : word w.mem (F s) sK = s.gpr .x4
  wMl : word w.mem (F s) sMl = s.gpr .x2
  lr : w.mem.readW (s.sp - 16) 64 = s.gpr .x30

theorem setup_ok {s : State} (hp : FPre s) :
    WP isa (.block Impl.RsaPkcs1Enc.AArch64.Front.setup) (entered s) (Ready s) := by
  have hBn := B_toNat hp
  have hsp2 := hp.sp2
  obtain hF : ∀ d n, d + n ≤ 272 → InRegions (entered s).wr (F s + BitVec.ofNat 64 d) n := fun d n h =>
    ⟨⟨F s, frameBytes⟩, by rw [entered_wr]; exact List.mem_cons_self .., Offset.contains_base _ h (by omega_arith)⟩
  -- The slots.
  rw [Impl.RsaPkcs1Enc.AArch64.Front.setup, WP.block_append_iff]
  refine WP.mono (Q := fun (u : State) => u.sp = F s ∧ u.rd = s.rd ∧ u.wr = (entered s).wr ∧ u.v = s.v ∧
      u.dit = s.dit ∧ u.gpr .x9 = F s ∧ (∀ r, r ≠ .x9 → u.gpr r = s.gpr r) ∧
      u.mem = (((entered s).mem.write (F s + BitVec.ofNat 64 152) 8 (s.gpr .x0)).write (F s + BitVec.ofNat 64 168) 8
        (s.gpr .x4)).write (F s + BitVec.ofNat 64 216) 8 (s.gpr .x2)) ?_ fun u hu => ?_
  · have h152 := hF 152 8 (by decide)
    have h168 := hF 168 8 (by decide)
    have h216 := hF 216 8 (by decide)
    oaep_run [sOut, sK, sMl, entered_sp, BitVec.add_zero, h152, h168, h216]
    and_intros
    all_goals first | trivial | (intro r hr; simp only [hr, ite_false]; rfl) | skip
  obtain ⟨usp, urd, uwr, uv, udit, u9, ugpr, um⟩ := hu
  rw [F_off, F_off, F_off, entered_mem, lr_addr] at um
  -- The moves.
  refine WP.mono (moves_ok 17 (Nat.le_refl _) (by rw [u9, usp]) (fun j hj => by
      rw [usp, uwr]; exact hF _ _ (by omega_arith))
    (fun j hj => ⟨argsR s, by rw [urd, hp.rd]; exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_singleton_self _)), by
      rw [usp, arg_addr]; exact arg_in s (by omega_arith)⟩)) fun w hm => ?_
  have hsp1 := hp.sp1
  obtain hsep : ∀ {d e : Nat}, d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ 2 ^ 64 → e + 8 ≤ 2 ^ 64 →
      Mem.Sep (B s + BitVec.ofNat 64 d) 8 (B s + BitVec.ofNat 64 e) 8 := @fun _ _ h₁ h₂ h₃ => Offset.sep _ h₁ h₂ h₃
  obtain hc : ∀ {d : Nat}, d + 8 ≤ 3776 → (stkR s).Contains (B s + BitVec.ofNat 64 d) 8 := @fun _ h =>
    Offset.contains_base _ h (by omega_arith)
  obtain fu : Frame [stkR s] s.mem u.mem := by
    rw [um]
    exact ((((Frame.refl _ _).write (List.mem_singleton_self _) _ (hc (by decide))).write
      (List.mem_singleton_self _) _ (hc (by decide))).write (List.mem_singleton_self _) _ (hc (by decide))).write
      (List.mem_singleton_self _) _ (hc (by decide))
  obtain hFd : ∀ {d : Nat}, 136 ≤ d → d + 8 ≤ 272 →
      w.mem.read (B s + BitVec.ofNat 64 (3488 + d)) 8 = u.mem.read (B s + BitVec.ofNat 64 (3488 + d)) 8 := @fun d h₁ h₂ =>
    hm.fr.read (r := ⟨B s + BitVec.ofNat 64 (3488 + d), 8⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr, usp, F_B]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)
  refine ⟨hm.sp.trans usp, hm.rd.trans urd, hm.wr.trans uwr, hm.v.trans uv, hm.dit.trans udit,
    fun r h9 h10 => (hm.gpr r h10).trans (ugpr r h9), fu.trans (hm.fr.sub fun r hr => ⟨stkR s,
      List.mem_singleton_self _, by rw [List.mem_singleton.mp hr, usp, F_B]; exact stk_sub s (by decide)⟩),
    fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · rw [← usp, hm.args j hj, usp, arg_addr, argA, rdW, um,
      Mem.read_write_sep (hsep (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      Mem.read_write_sep (hsep (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      Mem.read_write_sep (hsep (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      Mem.read_write_sep (hsep (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide), ← rdW,
      ← argA]
    rfl
  · rw [word, off, show sOut = 152 from rfl, F_off, rdW, hFd (by decide) (by decide), um,
      Mem.read_write_sep (hsep (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      Mem.read_write_sep (hsep (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      read_write_self]
  · rw [word, off, show sK = 168 from rfl, F_off, rdW, hFd (by decide) (by decide), um,
      Mem.read_write_sep (hsep (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      read_write_self]
  · rw [word, off, show sMl = 216 from rfl, F_off, rdW, hFd (by decide) (by decide), um, read_write_self]
  · rw [lr_addr, rdW, hm.fr.read (r := ⟨B s + BitVec.ofNat 64 3760, 8⟩) (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr, usp, F_B]
        exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide), um,
      Mem.read_write_sep (hsep (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      Mem.read_write_sep (hsep (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      Mem.read_write_sep (hsep (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      read_write_self]

/-! ## Memory apart from our stack -/

theorem bytes_eq {s : State} {m : Mem} (hf : Frame [stkR s] s.mem m) {p : Addr} {n : Nat}
    (hd : (stkR s).Disjoint ⟨p, n⟩) (hl : n ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p n = Spec.Rsa.bytesAt s.mem p n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun j hj => hf.bytes (R := ⟨p, n⟩) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd.symm) hl (List.mem_range.mp hj)

theorem words_eq {s : State} {m : Mem} (hf : Frame [stkR s] s.mem m) {p : Addr} {n : Nat}
    (hd : (stkR s).Disjoint ⟨p, n * 8⟩) (hl : p.toNat + n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt s.mem p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  exact hf.readW (r := ⟨p, n * 8⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd.symm) (by decide)

/-! ## The call -/

/-- What the callee reads: our read-only buffers, and the copies of the
stack arguments. -/
def rdC (s : State) : List Region := ro s ++ [⟨F s, 136⟩]

/-- The callee's entry. -/
abbrev cEntry (s w : State) : State := w.callEntry.withRegions (rdC s) s.wr

section
variable {s w : State} (hr : Ready s w)
include hr

theorem ce_arg {j : Nat} (hj : j < 17) : stackArg (cEntry s w) j = stackArg s j := by
  show w.mem.readW (w.sp + BitVec.ofNat 64 (8 * j)) 64 = _
  rw [hr.sp]; exact hr.args j hj

theorem ce_argA : stackArgAddr (cEntry s w) 0 = F s := by
  show w.sp + BitVec.ofNat 64 (8 * 0) = _; rw [hr.sp, Nat.mul_zero, BitVec.add_zero]

end

theorem call_pre {s w : State} (h : (FK 3776).pre s) (hr : Ready s w) : (DK 3488).pre (cEntry s w) := by
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    AArch64.abi, AArch64.argRegs, stackArgs17, List.append_eq,
    _root_.List.range, _root_.List.range.loop] at h
  sig_split h
  rename_i sp1 sp2 rd wr oM oN oE oD oI oP oQ oDP oDQ oQI oS oPr oA mN mE mD mI mP mQ mDP mDQ mQI mS mPr mA
    nS eS dS iS pS qS dpS dqS qiS sPr sA kO kM kN kE kD kI kP kQ kDP kDQ kQI kS kPr kA bO bM bN bE bD bI bP bQ
    bDP bDQ bQI bS bPr kv olk ilk el1 elk dl1 dlk pl1 plk ql1 qlk dpl qil dql slk prl
  sig_pre [Proof.RsaPkcs1Enc.decryptPrecomputedBodyContract, Proof.RsaPkcs1Enc.decryptPrecomputedBodySig,
    Proof.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs, stackArgs17, List.append_eq,
    _root_.List.range, _root_.List.range.loop]
  simp only [ce_argA hr, hr.gpr .x0 (by decide) (by decide), hr.gpr .x1 (by decide) (by decide), hr.gpr .x2 (by decide) (by decide),
    hr.gpr .x3 (by decide) (by decide), hr.gpr .x4 (by decide) (by decide), hr.gpr .x5 (by decide) (by decide),
    hr.gpr .x6 (by decide) (by decide), hr.gpr .x7 (by decide) (by decide), hr.sp,
    ce_arg hr (j := 0) (by decide), ce_arg hr (j := 1) (by decide), ce_arg hr (j := 2) (by decide),
    ce_arg hr (j := 3) (by decide), ce_arg hr (j := 4) (by decide), ce_arg hr (j := 5) (by decide),
    ce_arg hr (j := 6) (by decide), ce_arg hr (j := 7) (by decide), ce_arg hr (j := 8) (by decide),
    ce_arg hr (j := 9) (by decide), ce_arg hr (j := 10) (by decide), ce_arg hr (j := 11) (by decide),
    ce_arg hr (j := 12) (by decide), ce_arg hr (j := 13) (by decide), ce_arg hr (j := 14) (by decide),
    ce_arg hr (j := 15) (by decide), ce_arg hr (j := 16) (by decide)]
  obtain hBn : (B s).toNat + 3776 = s.sp.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat]
    omega_arith
  obtain hFn : (F s).toNat = (B s).toNat + 3488 := by
    rw [F_B, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  obtain eB : F s - BitVec.ofNat 64 3488 = B s := by rw [F_B]; exact BitVec.add_sub_cancel _ _
  obtain sB : Region.Sub ⟨B s, 3488⟩ (stkR s) := Region.sub_prefix (by decide)
  obtain sA : Region.Sub ⟨F s, 136⟩ (stkR s) := by
    have := fr_stk s (d := 0) (n := 136) (by decide); rwa [BitVec.add_zero] at this
  obtain kA' : (⟨B s, 3488⟩ : Region).Disjoint ⟨F s, 136⟩ := by
    rw [F_B]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_arith)
  obtain fw := hr.fr
  have := kv.2
  rw [bytes_eq fw kN (by omega_arith), bytes_eq fw kP (by omega_arith), bytes_eq fw kQ (by omega_arith),
    words_eq fw kPr bPr]
  simp only [eB]
  exact ⟨by omega_arith, by omega_arith, rfl, wr, oM, oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI, oS, oPr,
    (kO.sub_left sA).symm, mN, mE, mD, mI, mP, mQ, mDP, mDQ, mQI, mS, mPr, (kM.sub_left sA).symm, nS, eS, dS, iS,
    pS, qS, dpS, dqS, qiS, sPr, (kS.sub_left sA).symm, kO.sub_left sB, kM.sub_left sB, kN.sub_left sB,
    kE.sub_left sB, kD.sub_left sB, kI.sub_left sB, kP.sub_left sB, kQ.sub_left sB, kDP.sub_left sB,
    kDQ.sub_left sB, kQI.sub_left sB, kS.sub_left sB, kPr.sub_left sB, kA', bO, bM, bN, bE, bD, bI, bP, bQ, bDP,
    bDQ, bQI, bS, bPr, kv, olk, ilk, el1, elk, dl1, dlk, pl1, plk, ql1, qlk, dpl, qil, dql, slk, prl, h⟩

theorem pres_ne : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x0 := by decide

/-- What the callee decrypts. -/
def decOf (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (kOf s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (kOf s))

/-- After the call. -/
structure Called (s u : State) : Prop where
  sp : u.sp = F s
  rd : u.rd = s.rd
  wr : u.wr = (entered s).wr
  cs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = s.gpr r
  vs : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : Frame [outR s, mlR s, scrR s, stkR s] s.mem u.mem
  wOut : word u.mem (F s) sOut = s.gpr .x0
  wK : word u.mem (F s) sK = s.gpr .x4
  wMl : word u.mem (F s) sMl = s.gpr .x2
  lr : u.mem.readW (s.sp - 16) 64 = s.gpr .x30
  post : Proof.RsaPkcs1Enc.writtenMsgEnd u.mem (s.gpr .x0) (s.gpr .x2) (kOf s) ((u.gpr .x0).setWidth 32) (decOf s)

theorem call_covers {s w : State} (hp : FPre s) (hr : Ready s w) :
    Covers (rdC s ++ s.wr) (w.rd ++ w.wr) ∧ Covers s.wr w.wr := by
  obtain cw : Covers s.wr w.wr := Covers.of_mem fun r hr' => by
    rw [hr.wr, entered_wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr')
  refine ⟨Covers.append_left (Covers.append_left (Covers.left (Covers.of_mem fun r hr' => ?_)) ?_) cw.right, cw⟩
  · rw [hr.rd, hp.rd]; exact List.mem_append_left _ hr'
  · refine Covers.right (Covers.of_sub fun r hr' => ⟨⟨F s, frameBytes⟩, by rw [hr.wr, entered_wr]; exact List.mem_cons_self .., 0,
      ?_, ?_⟩)
    · rw [List.mem_singleton.mp hr']; exact (BitVec.add_zero _).symm
    · rw [List.mem_singleton.mp hr']; show 0 + 136 ≤ 272; decide

theorem call_ok {name : String} {callee : Prog isa}
    (hv : ∀ s, (DK 3488).pre s → ∃ t s', Exec isa callee s t s' ∧ abiPreserved s s' ∧ (DK 3488).post s s')
    (hd : 16 * callee.aarch64Depth ≤ 3488) {s w : State} (h : (FK 3776).pre s) (hr : Ready s w) :
    WP isa (.call name callee) w (Called s) := by
  have hp := fpre_of h
  have hsp1 := hp.sp1
  have hsp2 := hp.sp2
  obtain hBn := B_toNat hp
  obtain ⟨cr, cw⟩ := call_covers hp hr
  refine WP.callFV hv (call_pre h hr) cr cw (fun u hrd hwr hsp hf hcs hvs hpost => ?_)
    (by omega_arith)
  sig_post [Proof.RsaPkcs1Enc.decryptPrecomputedBodyContract, Proof.RsaPkcs1Enc.decryptPrecomputedBodySig,
    Proof.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs, stackArgs17, List.append_eq,
    _root_.List.range, _root_.List.range.loop] at hpost
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    AArch64.abi, AArch64.argRegs, stackArgs17, List.append_eq,
    _root_.List.range, _root_.List.range.loop] at h
  sig_split h
  rename_i sp1 sp2 rd wr oM oN oE oD oI oP oQ oDP oDQ oQI oS oPr oA mN mE mD mI mP mQ mDP mDQ mQI mS mPr mA
    nS eS dS iS pS qS dpS dqS qiS sPr sA kO kM kN kE kD kI kP kQ kDP kDQ kQI kS kPr kA bO bM bN bE bD bI bP bQ
    bDP bDQ bQI bS bPr kv olk ilk el1 elk dl1 dlk pl1 plk ql1 qlk dpl qil dql slk prl
  obtain fw := hr.fr
  have := kv.2
  simp only [ce_arg hr (j := 0) (by decide), ce_arg hr (j := 1) (by decide), ce_arg hr (j := 3) (by decide),
    ce_arg hr (j := 4) (by decide), ce_arg hr (j := 5) (by decide), ce_arg hr (j := 6) (by decide),
    ce_arg hr (j := 7) (by decide), ce_arg hr (j := 9) (by decide), ce_arg hr (j := 11) (by decide),
    hr.gpr .x0 (by decide) (by decide), hr.gpr .x2 (by decide) (by decide), hr.gpr .x3 (by decide) (by decide),
    hr.gpr .x4 (by decide) (by decide), hr.gpr .x5 (by decide) (by decide), hr.gpr .x6 (by decide) (by decide),
    hr.gpr .x7 (by decide) (by decide)] at hpost
  rw [bytes_eq fw kN (by omega_arith), bytes_eq fw kE (by omega_arith), bytes_eq fw kD (by omega_arith),
    bytes_eq fw kP (by omega_arith), bytes_eq fw kQ (by omega_arith),
    bytes_eq fw (n := (stackArg s 4).toNat) (by rw [← dpl]; exact kDP) (by omega_arith),
    bytes_eq fw (n := (stackArg s 6).toNat) (by rw [← dql]; exact kDQ) (by omega_arith),
    bytes_eq fw (n := (stackArg s 4).toNat) (by rw [← qil]; exact kQI) (by omega_arith),
    bytes_eq fw (n := (s.gpr .x4).toNat) (by rw [← ilk]; exact kI) (by omega_arith)] at hpost
  -- What the call leaves.
  obtain hdep : 16 * callee.aarch64Depth ≤ 3488 := hd
  obtain sBl : Region.Sub (below w.sp (16 * callee.aarch64Depth)) (stkR s) := by
    rw [hr.sp, below, F, BitVec.sub_sub, BitVec.ofNat_add_ofNat]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  obtain hkeep : ∀ d, d + 8 ≤ 288 → u.mem.readW (F s + BitVec.ofNat 64 d) 64 = w.mem.readW (F s + BitVec.ofNat 64 d) 64 :=
    fun d hd' => hf.readW (r := ⟨F s + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr' => by
      obtain sF : Region.Sub ⟨F s + BitVec.ofNat 64 d, 8⟩ (stkR s) := by
        rw [F_off]; exact stk_sub s (by omega_arith)
      rw [hp.wr] at hr'
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl
      · exact (hp.kO.sub_left sF)
      · exact (hp.kM.sub_left sF)
      · exact (hp.kS.sub_left sF)
      · rw [hr.sp]; exact Offset.disjoint_below _ (by omega_arith)) (by decide)
  obtain lrF : s.sp - 16 = F s + BitVec.ofNat 64 272 := by rw [F_off, lr_addr]
  refine ⟨hsp.trans hr.sp, hrd.trans hr.rd, hwr.trans hr.wr, fun r hr' h30 => ?_, fun r hr' => ?_, ?_,
    (hkeep 152 (by decide)).trans hr.wOut, (hkeep 168 (by decide)).trans hr.wK, (hkeep 216 (by decide)).trans hr.wMl,
    by rw [lrF, hkeep 272 (by decide), ← lrF]; exact hr.lr, hpost⟩
  · rw [hcs r hr' h30]
    exact hr.gpr r (pres_ne r hr').1 (pres_ne r hr').2.1
  · rw [hvs r hr', hr.v]
  · refine (fw.sub fun r hr' => ⟨stkR s, by simp, by rw [List.mem_singleton.mp hr']; exact fun _ h => h⟩).trans
      (hf.sub fun r hr' => ?_)
    rw [hp.wr] at hr'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact ⟨outR s, by simp, fun _ h => h⟩
    · exact ⟨mlR s, by simp, fun _ h => h⟩
    · exact ⟨scrR s, by simp, fun _ h => h⟩
    · exact ⟨stkR s, by simp, sBl⟩

/-! ## The message, first -/

theorem wordsAt_one (m : Mem) (p : Addr) : Spec.Rsa.wordsAt m p 1 = [m.readW p 64] := by
  simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]

theorem bytesAt_len (m : Mem) (p : Addr) (k : Nat) : (Spec.Rsa.bytesAt m p k).length = k := by
  simp [Spec.Rsa.bytesAt]

/-- What the callee left in `m0` with the result `R`: a message `M` at the
end of `out`, after zeros, its length at `msg_len`, and what the function
must leave instead. -/
structure DataO (s : State) (o : Spec.Rsa.Outcome) (m0 : Mem) (R : BitVec 64) (M : List Byte) : Prop where
  len : M.length ≤ kOf s
  out : Spec.Rsa.bytesAt m0 (s.gpr .x0) (kOf s) = List.replicate (kOf s - M.length) 0 ++ M
  ml : m0.readW (s.gpr .x2) 64 = BitVec.ofNat 64 M.length
  fin : ∀ m' : Mem, Spec.Rsa.bytesAt m' (s.gpr .x0) (kOf s) = M ++ List.replicate (kOf s - M.length) 0 →
    m'.readW (s.gpr .x2) 64 = m0.readW (s.gpr .x2) 64 →
    Spec.RsaPkcs1Enc.writtenMsg m' (s.gpr .x0) (s.gpr .x2) (kOf s) (R.setWidth 32) o

abbrev Data (s : State) := DataO s (decOf s)

theorem dataO_of {s : State} {o : Spec.Rsa.Outcome} {m0 : Mem} {R : BitVec 64}
    (h : Proof.RsaPkcs1Enc.writtenMsgEnd m0 (s.gpr .x0) (s.gpr .x2) (kOf s) (R.setWidth 32) o) :
    ∃ M, DataO s o m0 R M := by
  cases o with
  | ok M =>
    obtain ⟨hr, hb, hw⟩ := h
    rw [wordsAt_one] at hw
    have hl := congrArg List.length hb
    rw [bytesAt_len, List.length_append, List.length_replicate] at hl
    refine ⟨M, ⟨by omega_arith, hb, List.cons.inj hw |>.1, fun m' hb' hw' => ⟨hr, hb', ?_⟩⟩⟩
    rw [wordsAt_one, hw', List.cons.inj hw |>.1]
  | invalid =>
    obtain ⟨hr, hb, hw⟩ := h
    rw [wordsAt_one] at hw
    refine ⟨[], ⟨Nat.zero_le _, by rw [hb]; simp, List.cons.inj hw |>.1, fun m' hb' hw' => ⟨hr, ?_, ?_⟩⟩⟩
    · rw [hb']; simp
    · rw [wordsAt_one, hw', List.cons.inj hw |>.1]
  | fault =>
    obtain ⟨hr, hb, hw⟩ := h
    rw [wordsAt_one] at hw
    refine ⟨[], ⟨Nat.zero_le _, by rw [hb]; simp, List.cons.inj hw |>.1, fun m' hb' hw' => ⟨hr, ?_, ?_⟩⟩⟩
    · rw [hb']; simp
    · rw [wordsAt_one, hw', List.cons.inj hw |>.1]

/-! ## After the call: the frame and the working space -/

open VG.Proof.RsaOaep.AArch64 (retR nW cS zV cpV upd selV bM neg_and1 selWord copy8V frame_copy8 shr1_ofNat
  count_loop counter_ne counter_step clearLoop_ok Apart read_one byte64 byte_rt64 write1_apply pin_list)
open VG.Proof.Mgf1 (ifp ifn)

/-- `scratch`, whose first `oRsa` bytes are our working space. -/
abbrev S (s : State) : Addr := stackArg s 13

/-- What every piece after the call keeps. -/
structure En (s v : State) : Prop where
  sp : v.sp = F s
  rd : v.rd = s.rd
  wr : v.wr = (entered s).wr
  cs : ∀ r ∈ preserved, r ≠ .x30 → v.gpr r = s.gpr r
  vs : ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : Frame [outR s, mlR s, scrR s, stkR s] s.mem v.mem
  lr : v.mem.readW (s.sp - 16) 64 = s.gpr .x30

/-- Between the pieces after the call, from what the callee left in `m0`
with the result `R`: the frame and the working space as RSAES-OAEP's, with
`out`, `k`, `msg_len` and `R` in their slots. -/
structure Mid (s v : State) (m0 : Mem) (R : BitVec 64) (M : List Byte) (V : Nat → Byte) (W : Nat → BitVec 64) :
    Prop where
  en : En s v
  L : Lay v (F s) (S s)
  rep : Rep v.mem (F s) (S s) V W
  w19 : W 19 = s.gpr .x0
  w21 : W 21 = BitVec.ofNat 64 (kOf s)
  w27 : W 27 = s.gpr .x2
  w28 : W 28 = R
  ml : v.mem.readW (s.gpr .x2) 64 = m0.readW (s.gpr .x2) 64
  data : Data s m0 R M

/-- The message, then zeros: what the function leaves at `out`. -/
abbrev tgt (s : State) (M : List Byte) : List Byte := M ++ List.replicate (kOf s - M.length) 0

/-- `out`'s bytes as the callee left them. -/
abbrev OutAsIs (s v : State) (m0 : Mem) : Prop :=
  ∀ i < kOf s, v.mem (s.gpr .x0 + BitVec.ofNat 64 i) = m0 (s.gpr .x0 + BitVec.ofNat 64 i)

/-- `w`, the words of `k` bytes, which each pass of the shift covers. -/
abbrev wOf (s : State) : Nat := (kOf s + 7) / 8

/-- The bytes of the buffer that the shift reads, `16 w`: those cleared. -/
abbrev zK (s : State) : Nat := 16 * wOf s

/-- After `after`, and after each piece. -/
def St0 (s v : State) : Prop := ∃ m0 R M V W, Mid s v m0 R M V W ∧ OutAsIs s v m0
def St1 (s v : State) : Prop := ∃ m0 R M V W, Mid s v m0 R M V W ∧ OutAsIs s v m0 ∧
  ∀ x < zK s, V (oBuf + x) = 0
def St2 (s v : State) : Prop := ∃ m0 R M V W, Mid s v m0 R M V W ∧
  ∀ x < zK s, V (oBuf + x) = if x < kOf s then m0 (s.gpr .x0 + BitVec.ofNat 64 x) else 0
def St3 (s v : State) : Prop := ∃ m0 R M V W, Mid s v m0 R M V W ∧
  ∀ i < kOf s, V (oBuf + i) = (tgt s M).getD i 0
def St4 (s v : State) : Prop := ∃ m0 R M V W, Mid s v m0 R M V W ∧
  Spec.Rsa.bytesAt v.mem (s.gpr .x0) (kOf s) = tgt s M

theorem k_le {s : State} (hp : FPre s) : kOf s ≤ 1024 := hp.kv.2

theorem scr8192 {s : State} (hp : FPre s) : oRsa ≤ (stackArg s 14).toNat * 8 := by
  have := hp.slk; have := hp.kv.1; unfold Spec.Rsa.scratchWords oRsa at *; omega_arith

theorem sR_sub {s : State} (hp : FPre s) : Region.Sub ⟨S s, oRsa⟩ (scrR s) := Region.sub_prefix (scr8192 hp)

theorem retR_eq (s : State) : retR (F s) = ⟨B s + BitVec.ofNat 64 3472, 16⟩ := by
  show (⟨F s - BitVec.ofNat 64 16, 16⟩ : Region) = _
  rw [F_B, show (3488 : Nat) = 3472 + 16 from rfl, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
    BitVec.add_sub_cancel]

theorem retR_stk (s : State) : Region.Sub (retR (F s)) (stkR s) := by rw [retR_eq]; exact stk_sub s (by decide)

theorem frame_stk (s : State) : Region.Sub ⟨F s, frameBytes⟩ (stkR s) := by
  have := fr_stk s (d := 0) (n := 272) (by decide); rwa [BitVec.add_zero] at this

theorem geo_of {s : State} (hp : FPre s) : Geo (F s) (S s) := by
  have hBn := B_toNat hp
  have hsp2 := hp.sp2
  have hbS := hp.bS
  have h8 := scr8192 hp
  have hFn : (F s).toNat = (B s).toNat + 3488 := by
    rw [F_B, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  refine ⟨by omega_arith, by unfold frameBytes; omega_arith, by show (stackArg s 13).toNat + oRsa ≤ 2 ^ 64; omega_arith,
    (hp.kS.sub_left (frame_stk s)).sub_right (sR_sub hp), (hp.kS.sub_left (retR_stk s)).sub_right (sR_sub hp), ?_⟩
  rw [retR_eq, F_B]
  exact Offset.disjoint _ (.inl (by decide)) (by omega_arith) (by unfold frameBytes; omega_arith)

theorem lay_of {s v : State} (hp : FPre s) (h : En s v) (hs : word v.mem (F s) sScr = S s) : Lay v (F s) (S s) :=
  ⟨h.sp, Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.wr, entered_wr]; exact List.mem_cons_self ..,
    Covers.of_sub fun r hr => ⟨scrR s, by rw [h.wr, entered_wr, hp.wr]; simp, 0,
      by rw [List.mem_singleton.mp hr]; exact (BitVec.add_zero _).symm,
      by rw [List.mem_singleton.mp hr]; have := scr8192 hp; dsimp only; omega_arith⟩, hs, geo_of hp⟩

theorem rep0 (m : Mem) (F S : Addr) : Rep m F S (fun o => m (off S o)) (fun k => word m F (8 * k)) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem ofNat_k (s : State) : BitVec.ofNat 64 (kOf s) = s.gpr .x4 :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (BitVec.isLt _))

/-- Writes within our stack keep what lies apart from it. -/
theorem stk_keepW {s : State} {m m' : Mem} (hf : Frame [stkR s] m m') {a : Addr} {R : Region}
    (hR : (stkR s).Disjoint R) (ha : R.Contains a 8) : m'.readW a 64 = m.readW a 64 :=
  hf.readW ha (fun r hr => by rw [List.mem_singleton.mp hr]; exact hR.symm) (by decide)

theorem after_ok {s u : State} (hp : FPre s) (hc : Called s u) :
    WP isa (.block Impl.RsaPkcs1Enc.AArch64.Front.after) u (St0 s) := by
  have hBn := B_toNat hp
  have hsp2 := hp.sp2
  obtain hFr : ∀ d n, d + n ≤ 272 → InRegions u.wr (F s + BitVec.ofNat 64 d) n := fun d n h =>
    ⟨⟨F s, frameBytes⟩, by rw [hc.wr, entered_wr]; exact List.mem_cons_self .., Offset.contains_base _ h (by omega_arith)⟩
  obtain e392 : F s + BitVec.ofNat 64 392 = stackArgAddr s 13 := arg_addr s 13
  obtain hA : InRegions (u.rd ++ u.wr) (F s + BitVec.ofNat 64 392) 8 :=
    ⟨argsR s, by rw [hc.rd, hp.rd]; simp, by rw [e392]; exact arg_in s (by decide)⟩
  -- Our stack arguments, apart from what the callee writes.
  obtain hS13 : u.mem.read (F s + BitVec.ofNat 64 392) 8 = S s := by
    rw [← rdW, e392]
    refine hc.fr.readW (arg_in s (by decide)) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.dOA.symm
    · exact hp.dMA.symm
    · exact hp.dSA.symm
    · rw [argsR, stackArgAddr, Nat.mul_zero, BitVec.add_zero, sp_B]
      exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith)
  refine WP.mono (Q := fun (v : State) => v.sp = u.sp ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.v = u.v ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → v.gpr r = u.gpr r) ∧
      v.mem = (u.mem.write (F s + BitVec.ofNat 64 224) 8 (u.gpr .x0)).write (F s + BitVec.ofNat 64 96) 8 (S s)) ?_
    fun v ⟨vsp, vrd, vwr, vv, vg, vm⟩ => ?_
  · have h224 := hFr 224 8 (by decide)
    have h96 := hFr 96 8 (by decide)
    obtain hS' : (u.mem.write (F s + BitVec.ofNat 64 224) 8 (u.gpr .x0)).read (F s + BitVec.ofNat 64 392) 8 = S s := by
      rw [Mem.read_write_sep (Offset.sep _ (.inr (by decide)) (by decide) (by decide)) (by decide), hS13]
    oaep_run [Impl.RsaPkcs1Enc.AArch64.Front.after, mvArg, arg, frameBytes, sR, sScr, hc.sp, BitVec.add_zero, h224,
      h96, hA, hS']
    exact ⟨trivial, trivial, trivial, trivial, fun r h9 h10 => by simp only [h9, h10, ite_false], trivial⟩
  -- The memory: two words of the frame written.
  rw [F_off, F_off] at vm
  obtain fv : Frame [stkR s] u.mem v.mem := by
    rw [vm]
    exact ((Frame.refl _ _).write (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega_arith))).write
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega_arith))
  obtain hw : ∀ d, d + 8 ≤ 272 → d + 8 ≤ 96 ∨ 104 ≤ d → d + 8 ≤ 224 ∨ 232 ≤ d →
      word v.mem (F s) d = word u.mem (F s) d := fun d h1 h2 h3 => by
    rw [word, word, off, F_off, rdW, rdW, vm,
      Mem.read_write_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.read_write_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
  obtain ⟨M, hD⟩ := dataO_of hc.post
  obtain hen : En s v := ⟨vsp.trans hc.sp, vrd.trans hc.rd, vwr.trans hc.wr,
    fun r hr h30 => (vg r (pres_ne r hr).1 (pres_ne r hr).2.1).trans (hc.cs r hr h30),
    fun r hr => by rw [vv]; exact hc.vs r hr,
    hc.fr.trans (fv.sub fun r hr => ⟨stkR s, by simp, by rw [List.mem_singleton.mp hr]; exact fun _ h => h⟩),
    by rw [lr_addr, rdW, vm,
      Mem.read_write_sep (Offset.sep _ (.inr (by decide)) (by omega_arith) (by omega_arith)) (by decide),
      Mem.read_write_sep (Offset.sep _ (.inr (by decide)) (by omega_arith) (by omega_arith)) (by decide),
      ← rdW, ← lr_addr]; exact hc.lr⟩
  obtain hslot : word v.mem (F s) sScr = S s := by
    rw [word, off, show sScr = 96 from rfl, F_off, rdW, vm, read_write_self]
  refine ⟨u.mem, u.gpr .x0, M, _, _, ⟨hen, lay_of hp hen hslot, rep0 v.mem (F s) (S s),
    (hw 152 (by decide) (by decide) (by decide)).trans hc.wOut,
    ((hw 168 (by decide) (by decide) (by decide)).trans hc.wK).trans (ofNat_k s).symm,
    (hw 216 (by decide) (by decide) (by decide)).trans hc.wMl, ?_,
    stk_keepW fv hp.kM (Region.contains_self _ _), hD⟩, fun i hi => ?_⟩
  · show word v.mem (F s) 224 = _
    rw [word, off, F_off, rdW, vm,
      Mem.read_write_sep (Offset.sep _ (.inr (by decide)) (by omega_arith) (by omega_arith)) (by decide),
      read_write_self]
  · exact fv.bytes (R := outR s) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.kO.symm)
      (by have := hp.bO; dsimp only; omega_arith) (by show i < (s.gpr .x1).toNat; rw [hp.olk]; exact hi)

/-! ## After the call: the pieces -/

/-- The regions a piece writes are within `out`, `scratch` and our stack. -/
theorem step_sub {s : State} (hp : FPre s) {ws : List Region} (hws : ∀ r ∈ ws, r = outR s) :
    ∀ r ∈ (⟨F s, frameBytes⟩ :: ⟨S s, oRsa⟩ :: retR (F s) :: ws), ∃ r' ∈ [outR s, mlR s, scrR s, stkR s],
      Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | hr
  · exact ⟨stkR s, by simp, frame_stk s⟩
  · exact ⟨scrR s, by simp, sR_sub hp⟩
  · exact ⟨stkR s, by simp, retR_stk s⟩
  · rw [hws r hr]; exact ⟨outR s, by simp, fun _ h => h⟩

/-- A region apart from `out`, `scratch` and our stack is apart from what a
piece writes. -/
theorem step_apart {s : State} (hp : FPre s) {ws : List Region} (hws : ∀ r ∈ ws, r = outR s) {X : Region}
    (hO : X.Disjoint (outR s)) (hS : X.Disjoint (scrR s)) (hK : X.Disjoint (stkR s)) :
    ∀ r ∈ (⟨F s, frameBytes⟩ :: ⟨S s, oRsa⟩ :: retR (F s) :: ws), X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | hr
  · exact hK.sub_right (frame_stk s)
  · exact hS.sub_right (sR_sub hp)
  · exact hK.sub_right (retR_stk s)
  · rw [hws r hr]; exact hO

theorem lr_apart {s : State} (hp : FPre s) : (⟨s.sp - 16, 8⟩ : Region).Disjoint (outR s) ∧
    (⟨s.sp - 16, 8⟩ : Region).Disjoint (scrR s) ∧ ∀ r ∈ [⟨F s, frameBytes⟩, retR (F s)], (⟨s.sp - 16, 8⟩ : Region).Disjoint r := by
  have hBn := B_toNat hp
  have hsp2 := hp.sp2
  obtain hsub : Region.Sub ⟨s.sp - 16, 8⟩ (stkR s) := by rw [lr_addr]; exact stk_sub s (by decide)
  refine ⟨(hp.kO.sub_left hsub), (hp.kS.sub_left hsub), fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [lr_addr, F_B]; exact Offset.disjoint _ (.inr (by decide)) (by omega_arith) (by unfold frameBytes; omega_arith)
  · rw [lr_addr, retR_eq]; exact Offset.disjoint _ (.inr (by decide)) (by omega_arith) (by omega_arith)

theorem Mid.step {s v v' : State} {m0 : Mem} {R : BitVec 64} {M : List Byte} {V V' : Nat → Byte}
    {W W' : Nat → BitVec 64} (hp : FPre s) (h : Mid s v m0 R M V W) {ws : List Region}
    (hws : ∀ r ∈ ws, r = outR s) (hS : Step (F s) (S s) ws v v') (hR : Rep v'.mem (F s) (S s) V' W')
    (hW : ∀ j, j = 12 ∨ j = 19 ∨ j = 21 ∨ j = 27 ∨ j = 28 → W' j = W j) :
    Mid s v' m0 R M V' W' := by
  obtain ⟨lO, lS, lF⟩ := lr_apart hp
  refine ⟨⟨hS.sp.trans h.en.sp, hS.rd.trans h.en.rd, hS.wr.trans h.en.wr,
    fun r hr h30 => (hS.cs r hr h30).trans (h.en.cs r hr h30), fun r hr => (hS.vec r hr).trans (h.en.vs r hr),
    h.en.fr.trans (hS.frame.sub (step_sub hp hws)), ?_⟩,
    h.L.congr hS.sp hS.wr (by rw [show sScr = 8 * 12 from rfl, hR.fr 12 (by decide), h.rep.fr 12 (by decide),
      hW 12 (by simp)]), hR, (hW 19 (by simp)).trans h.w19, (hW 21 (by simp)).trans h.w21,
    (hW 27 (by simp)).trans h.w27, (hW 28 (by simp)).trans h.w28, ?_, h.data⟩
  · rw [hS.frame.readW (r := ⟨s.sp - 16, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact h.en.lr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hr
    · exact lF _ (by simp)
    · exact lS.sub_right (sR_sub hp)
    · exact lF _ (by simp)
    · rw [hws r hr]; exact lO
  · rw [hS.frame.readW (r := mlR s) (Region.contains_self _ _) (step_apart hp hws hp.dOM.symm hp.dMS hp.kM.symm)
      (by decide)]
    exact h.ml

theorem nil_ws {s : State} : ∀ r ∈ ([] : List Region), r = outR s := fun _ h => absurd h List.not_mem_nil

/-- `out`'s bytes, through a piece that writes only in the frame and our working space. -/
theorem out_keep {s v v' : State} (hp : FPre s) (hS : Step (F s) (S s) [] v v') {i : Nat} (hi : i < kOf s) :
    v'.mem (s.gpr .x0 + BitVec.ofNat 64 i) = v.mem (s.gpr .x0 + BitVec.ofNat 64 i) := by
  refine hS.frame.bytes (R := outR s) (fun r hr => ?_) (by have := hp.bO; dsimp only; omega_arith)
    (by show i < (s.gpr .x1).toNat; rw [hp.olk]; exact hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.kO.sub_left (frame_stk s)).symm
  · exact hp.dOS.sub_right (sR_sub hp)
  · exact (hp.kO.sub_left (retR_stk s)).symm

/-- `w`, from `k`. -/
theorem words_bv {k : Nat} (hk : k ≤ 1024) :
    BitVec.ofNat 64 (k + 7) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show k + 7 < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show (k + 7) / 8 < 2 ^ 64 by omega_arith)]

theorem words_bv' {k : Nat} (hk : k ≤ 1024) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) := by
  rw [BitVec.ofNat_add_ofNat]; exact words_bv hk

theorem clear_ok {s v : State} (hp : FPre s) (h : St0 s v) :
    WP isa Impl.RsaPkcs1Enc.AArch64.Front.clearK v (St1 s) := by
  obtain ⟨m0, R, M, V, W, hm, ho⟩ := h
  have hk := k_le hp
  have L := hm.L
  obtain h96 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  obtain h168 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have hs : v.mem.read (F s + BitVec.ofNat 64 96) 8 = S s := L.slot
  obtain rk := hm.rep.rd8 (d := 168) (k := 21) rfl (by decide) hm.w21
  unfold Impl.RsaPkcs1Enc.AArch64.Front.clearK
  refine WP.seq (WP.mono (Q := fun (u : State) => u.mem = v.mem ∧ u.rd = v.rd ∧ u.wr = v.wr ∧ u.sp = v.sp ∧
      u.v = v.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = v.gpr r) ∧ u.gpr .x11 = off (S s) oBuf ∧
      u.gpr .x12 = BitVec.ofNat 64 (wOf s + wOf s) ∧ u.gpr .x13 = 0) ?_
    fun u ⟨um, urd, uwr, usp, uv, ucs, x11, x12, x13⟩ => ?_)
  · oaep_run [scr, VG.Impl.RsaOaep.AArch64.Mgf1.scr, VG.Impl.RsaOaep.AArch64.lay, sScr, sK, oBuf, h96, h168, L.sp,
      hs, rk, words_bv hk, words_bv' hk, BitVec.ofNat_add_ofNat,
      show BitVec.setWidth 64 (0 : BitVec 16) <<< 0 = 0#64 by decide]
    oaep_fin
  obtain S1 : Step (F s) (S s) [] v u := Step.blk _ urd uwr usp uv ucs um
  have cB : oBuf = 1024 := rfl
  have cR : oRsa = 8192 := rfl
  have ew : wOf s = (kOf s + 7) / 8 := rfl
  have ez : zK s = 16 * wOf s := rfl
  refine WP.mono (clearLoop_ok (L.congr usp uwr (by rw [um])) (um ▸ hm.rep) (o := oBuf) (n := wOf s + wOf s)
    (by have := hp.kv.1; omega_arith) (by omega_arith) x11 x12 x13 []) fun w ⟨_, Sw, Rw⟩ =>
    ⟨m0, R, M, _, W, hm.step hp nil_ws (S1.trans Sw) Rw fun _ _ => rfl,
      fun i hi => (out_keep hp (S1.trans Sw) hi).trans (ho i hi), fun x hx => ?_⟩
  simp only [zV]; rw [ifp (by omega_arith)]

theorem cin_ok {s v : State} (hp : FPre s) (h : St1 s v) :
    WP isa Impl.RsaPkcs1Enc.AArch64.Front.copyIn v (St2 s) := by
  obtain ⟨m0, R, M, V, W, hm, ho, hz⟩ := h
  have hk := k_le hp
  have hk1 := hp.kv.1
  have L := hm.L
  obtain h96 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  obtain h152 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 152) 8 := L.ld (d := 152) (by decide)
  obtain h168 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have hs : v.mem.read (F s + BitVec.ofNat 64 96) 8 = S s := L.slot
  obtain ro := hm.rep.rd8 (d := 152) (k := 19) rfl (by decide) hm.w19
  obtain rk := hm.rep.rd8 (d := 168) (k := 21) rfl (by decide) hm.w21
  refine WP.seq (WP.mono (Q := fun (u : State) => u.mem = v.mem ∧ u.rd = v.rd ∧ u.wr = v.wr ∧ u.sp = v.sp ∧
      u.v = v.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = v.gpr r) ∧ u.gpr .x11 = s.gpr .x0 ∧
      u.gpr .x12 = off (S s) oBuf ∧ u.gpr .x13 = BitVec.ofNat 64 (kOf s)) ?_
    fun u ⟨um, urd, uwr, usp, uv, ucs, x11, x12, x13⟩ => ?_)
  · oaep_run [scr, VG.Impl.RsaOaep.AArch64.Mgf1.scr, VG.Impl.RsaOaep.AArch64.lay, sScr, sOut, sK, oBuf, h96, h152,
      h168, L.sp, hs, ro, rk]
    oaep_fin
  obtain S1 : Step (F s) (S s) [] v u := Step.blk _ urd uwr usp uv ucs um
  obtain L1 : Lay u (F s) (S s) := L.congr usp uwr (by rw [um])
  obtain R1 : Rep u.mem (F s) (S s) V W := um ▸ hm.rep
  have cR : oRsa = 8192 := rfl
  have cB : oBuf = 1024 := rfl
  have hbO := hp.bO
  have holk := hp.olk
  obtain hout : ∀ i < kOf s, Region.Contains (outR s) (off (s.gpr .x0) i) 1 := fun i hi =>
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine WP.mono (VG.Proof.RsaOaep.AArch64.copyLoop_ok L1 R1 (A := s.gpr .x0) (b := oBuf) (n := kOf s)
    (by omega_arith) (by omega_arith)
    (fun i hi => ⟨outR s, by rw [uwr, hm.en.wr, entered_wr, hp.wr]; simp, hout i hi⟩)
    (fun i hi j hj he => hp.dOS (off (s.gpr .x0) i) (hout i hi) (by
      rw [he]; exact (sR_sub hp) _ (cS (S s) (o := oBuf + j) (n := 1) (by omega_arith))))
    x11 x12 x13 []) fun w ⟨Lw, Sw, Rw⟩ => ?_
  refine ⟨m0, R, M, _, W, hm.step hp nil_ws (S1.trans Sw) Rw fun _ _ => rfl, fun x hx => ?_⟩
  simp only [cpV]
  by_cases hxk : x < kOf s
  · rw [ifp (by omega_arith), ifp hxk, Nat.add_sub_cancel_left, um]; exact ho x hxk
  · rw [ifn (by omega_arith), ifn hxk]; exact hz x hx

/-! ## The shift, one pass for each bit of `k` -/

theorem regs5 {P : Reg → Prop} (h17 : P .x17) (h14 : P .x14) (h9 : P .x9) (h8 : P .x8) (h7 : P .x7) :
    ∀ r ∈ [Reg.x17, .x14, .x9, .x8, .x7], P r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- RSAES-OAEP's `passBody_ok`, which also keeps `x7`. -/
theorem passBodyK_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {d j : Nat} {b : Bool} (hj : oBuf + d + j + 8 ≤ oRsa)
    (h11 : u.gpr .x11 = off S (oBuf + j)) (h12 : u.gpr .x12 = off S (oBuf + d + j)) (h15 : u.gpr .x15 = bM b)
    (ws : List Region) :
    WP isa (.block passBody) u fun u' => Lay u' F S ∧ Step F S ws u u' ∧
      Rep u'.mem F S (copy8V V (oBuf + j) (if b then oBuf + d + j else oBuf + j)) W ∧
      u'.gpr .x11 = off S (oBuf + j + 8) ∧ u'.gpr .x12 = off S (oBuf + d + j + 8) ∧ u'.gpr .x15 = bM b ∧
      u'.gpr .x13 = u.gpr .x13 - BitVec.ofNat 64 1 ∧
      (∀ r ∈ [Reg.x17, .x14, .x9, .x8, .x7], u'.gpr r = u.gpr r) := by
  obtain r1 : InRegions (u.rd ++ u.wr) (off S (oBuf + j)) 8 := L.sld (by omega_arith)
  obtain r2 : InRegions (u.rd ++ u.wr) (off S (oBuf + d + j)) 8 := L.sld (by omega_arith)
  obtain w1 : InRegions u.wr (off S (oBuf + j)) 8 := L.sst (by omega_arith)
  let src := if b then oBuf + d + j else oBuf + j
  obtain hs : src + 8 ≤ oRsa := by dsimp [src]; split <;> omega_arith
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.writeW (off S (oBuf + j))
      (u.mem.readW (off S src) 64) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧
      (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S (oBuf + j) + BitVec.ofNat 64 8 ∧
      u'.gpr .x12 = off S (oBuf + d + j) + BitVec.ofNat 64 8 ∧ u'.gpr .x15 = bM b ∧
      u'.gpr .x13 = u.gpr .x13 - BitVec.ofNat 64 1 ∧ (∀ r ∈ [Reg.x17, .x14, .x9, .x8, .x7], u'.gpr r = u.gpr r)) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x15, x13, xk⟩ => ?_
  · cases b <;>
      oaep_run [passBody, h11, h12, h15, BitVec.add_zero, r1, r2, w1, selWord, src, Mem.readW, Mem.writeW,
        Bool.false_eq_true, ite_false, ite_true]
    all_goals and_intros <;> first | trivial | exact cs_rfl | exact regs5 rfl rfl rfl rfl rfl
  obtain R' : Rep u'.mem F S (copy8V V (oBuf + j) src) W := by
    rw [hm]; exact R.copy8 L.geo (by omega_arith) hs
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], ?_⟩, R', x11.trans (off_off S _ 8),
    x12.trans (off_off S _ 8), x15, x13, xk⟩
  · rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]
  · rw [hm]; exact frame_copy8 (by omega_arith)

/-- A pass's loop over `n` words, eight bytes per iteration. -/
theorem passLoopK_ok {u₀ : State} {F S : Addr} (L : Lay u₀ F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u₀.mem F S V W) {d n : Nat} {b : Bool} (hd2 : d ≤ 1024) (hn0 : 0 < n) (hn : 8 * n ≤ 1024)
    (h11 : u₀.gpr .x11 = off S oBuf) (h12 : u₀.gpr .x12 = off S (oBuf + d)) (h15 : u₀.gpr .x15 = bM b)
    (h13 : u₀.gpr .x13 = BitVec.ofNat 64 n) (ws : List Region) :
    WP isa (.loop (.block passBody) (.nonzero .x .x13)) u₀ fun u =>
      Lay u F S ∧ Step F S ws u₀ u ∧ Rep u.mem F S (selV V d b (8 * n)) W ∧
        ∀ r ∈ [Reg.x17, .x14, .x9, .x8, .x7], u.gpr r = u₀.gpr r := by
  have c : oRsa = 8192 := rfl
  have cb : oBuf = 1024 := rfl
  refine WP.mono (count_loop hn0 (fun j u => Lay u F S ∧ Step F S ws u₀ u ∧
      Rep u.mem F S (selV V d b (8 * j)) W ∧ u.gpr .x11 = off S (oBuf + 8 * j) ∧
      u.gpr .x12 = off S (oBuf + d + 8 * j) ∧
      u.gpr .x15 = bM b ∧ u.gpr .x13 = BitVec.ofNat 64 (n - j) ∧
      ∀ r ∈ [Reg.x17, .x14, .x9, .x8, .x7], u.gpr r = u₀.gpr r)
    (fun j hj u ⟨Lu, Su, Ru, u11, u12, u15, u13, uk⟩ => ?_)
    ⟨L, Step.refl _ _ _ _, by
      refine (congrArg (fun V' => Rep _ F S V' _) (funext fun x => ?_)).mp R
      simp only [selV]; rw [ifn (by omega_arith)], by rw [h11]; rfl, by rw [h12]; rfl, h15,
      by rw [h13, Nat.sub_zero], fun _ _ => rfl⟩)
    fun u ⟨Lu, Su, Ru, _, _, _, _, uk⟩ => ⟨Lu, Su, Ru, uk⟩
  refine WP.mono (passBodyK_ok Lu Ru (d := d) (j := 8 * j) (by omega_arith) u11 u12 u15 ws)
    fun u' ⟨L', S', R', x11, x12, x15, x13, xk⟩ => ⟨⟨L', Su.trans S', ?_, ?_, ?_, x15, ?_,
      fun r hr => (xk r hr).trans (uk r hr)⟩, ?_⟩
  · refine (congrArg (fun V' => Rep u'.mem F S V' W) (funext fun x => ?_)).mp R'
    dsimp only [copy8V]
    by_cases hx : oBuf + 8 * j ≤ x ∧ x < oBuf + 8 * j + 8
    · rw [ifp hx]
      cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, selV]
      · rw [ifn (by omega_arith), ifp (by omega_arith)]
        congr 1; omega_arith
      · rw [ifn (by omega_arith), ifp (by omega_arith)]
        congr 1; omega_arith
    · rw [ifn hx]
      simp only [selV]
      obtain he : (oBuf ≤ x ∧ x < oBuf + 8 * j) ↔ (oBuf ≤ x ∧ x < oBuf + 8 * (j + 1)) := by omega_arith
      simp only [he]
  · rw [x11]; congr 1
  · rw [x12]; congr 1
  · rw [x13, u13, counter_step hj (by omega_arith)]
  · rw [x13, u13, counter_step hj (by omega_arith)]; exact counter_ne hj (by omega_arith)

/-- A pass of the shift over `n` words, by `d` under bit 0 of `a`, and the
next pass's `a / 2`, `2 d`, `c / 2`. -/
theorem passK_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {a c d n : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) (hd2 : d ≤ 1024) (hn0 : 0 < n)
    (hn : 8 * n ≤ 1024) (h17 : u.gpr .x17 = off S oBuf) (h14 : u.gpr .x14 = BitVec.ofNat 64 d)
    (h9 : u.gpr .x9 = BitVec.ofNat 64 a) (h8 : u.gpr .x8 = BitVec.ofNat 64 c) (h7 : u.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa Impl.RsaPkcs1Enc.AArch64.Front.passK u fun u' => Lay u' F S ∧ Step F S [] u u' ∧
      Rep u'.mem F S (selV V d (decide (a % 2 = 1)) (8 * n)) W ∧ u'.gpr .x17 = off S oBuf ∧
      u'.gpr .x14 = BitVec.ofNat 64 (2 * d) ∧ u'.gpr .x9 = BitVec.ofNat 64 (a / 2) ∧
      u'.gpr .x8 = BitVec.ofNat 64 (c / 2) ∧ u'.gpr .x7 = BitVec.ofNat 64 n := by
  obtain ha2 : (BitVec.ofNat 64 a).toNat % 2 = a % 2 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  unfold Impl.RsaPkcs1Enc.AArch64.Front.passK
  refine WP.seq (WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧ u'.gpr .x11 = off S oBuf ∧
      u'.gpr .x12 = off S oBuf + BitVec.ofNat 64 d ∧ u'.gpr .x15 = bM (decide (a % 2 = 1)) ∧
      u'.gpr .x13 = BitVec.ofNat 64 n ∧ u'.gpr .x17 = off S oBuf ∧ u'.gpr .x14 = BitVec.ofNat 64 d ∧
      u'.gpr .x9 = BitVec.ofNat 64 a ∧ u'.gpr .x8 = BitVec.ofNat 64 c ∧ u'.gpr .x7 = BitVec.ofNat 64 n) ?_
    fun u1 ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x15, x13, x17, x14, x9, x8, x7⟩ => ?_)
  · oaep_run [mov, h17, h14, h9, h8, h7, BitVec.or_self, show BitVec.setWidth 64 (1 : BitVec 16) <<< 0 = 1 by decide,
      show BitVec.setWidth 64 (0 : BitVec 16) <<< 0 = 0#64 by decide, neg_and1, ha2]
    oaep_fin
  obtain S1 : Step F S [] u u1 := Step.blk _ hrd hwr hsp hv hcs hm
  refine WP.seq (WP.mono (passLoopK_ok (L.congr hsp hwr (by rw [hm])) (hm ▸ R) hd2 hn0 hn x11
    (x12.trans (off_off S oBuf d)) x15 x13 []) fun u2 ⟨L2, S2, R2, k2⟩ => ?_)
  refine WP.mono (Q := fun (u' : State) => u'.mem = u2.mem ∧ u'.rd = u2.rd ∧ u'.wr = u2.wr ∧ u'.sp = u2.sp ∧
      u'.v = u2.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u2.gpr r) ∧ u'.gpr .x17 = u2.gpr .x17 ∧
      u'.gpr .x14 = u2.gpr .x14 + u2.gpr .x14 ∧ u'.gpr .x9 = u2.gpr .x9 >>> 1 ∧
      u'.gpr .x8 = u2.gpr .x8 >>> 1 ∧ u'.gpr .x7 = u2.gpr .x7) ?_
    fun u3 ⟨hm3, hrd3, hwr3, hsp3, hv3, hcs3, x17', x14', x9', x8', x7'⟩ => ?_
  · oaep_run []
    oaep_fin
  obtain e17 := k2 .x17 (by simp)
  obtain e14 := k2 .x14 (by simp)
  obtain e9 := k2 .x9 (by simp)
  obtain e8 := k2 .x8 (by simp)
  obtain e7 := k2 .x7 (by simp)
  refine ⟨L2.congr hsp3 hwr3 (by rw [hm3]), S1.trans (S2.trans (Step.blk _ hrd3 hwr3 hsp3 hv3 hcs3 hm3)),
    hm3 ▸ R2, by rw [x17', e17, x17], by rw [x14', e14, x14, BitVec.ofNat_add_ofNat, Nat.two_mul],
    by rw [x9', e9, x9, shr1_ofNat ha], by rw [x8', e8, x8, shr1_ofNat hc], by rw [x7', e7, x7]⟩

/-- The buffer before the shift, as a function of the index: its first `k`
bytes, and zeros after them. -/
def bufK (V : Nat → Byte) (k x : Nat) : Byte := if x < k then V (oBuf + x) else 0

/-- Whether passes remain after pass `p`: while `k / 2^(p+1)`, what `x8`
holds then, is not zero, that is for the `bitLength k = log2 k + 1` passes. -/
theorem bits_ne {k p : Nat} (hk : k ≠ 0) (hk64 : k < 2 ^ 64) (hp : p < k.log2 + 1) :
    (BitVec.ofNat 64 (k / 2 ^ (p + 1)) != 0) = decide (p + 1 ≠ k.log2 + 1) := by
  by_cases h : p + 1 = k.log2 + 1
  · rw [h, Nat.div_eq_of_lt Nat.lt_log2_self]; simp
  · obtain hle : 2 ^ (p + 1) ≤ k :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega_arith)) (Nat.log2_self_le hk)
    obtain hpos : 0 < k / 2 ^ (p + 1) := Nat.div_pos hle (Nat.two_pow_pos _)
    obtain hne : BitVec.ofNat 64 (k / 2 ^ (p + 1)) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hk64)] at this
      exact Nat.pos_iff_ne_zero.mp hpos this
    rw [decide_eq_true h, bne_iff_ne]; exact hne

/-- Before pass `p` of the shift by `A` of the buffer's first `k` bytes,
over `w` words. -/
structure ShiftK (u₀ : State) (F S : Addr) (V₀ : Nat → Byte) (W : Nat → BitVec 64) (A k w p : Nat) (t : State) :
    Prop where
  L : Lay t F S
  st : Step F S [] u₀ t
  x17 : t.gpr .x17 = off S oBuf
  x14 : t.gpr .x14 = BitVec.ofNat 64 (2 ^ p)
  x9 : t.gpr .x9 = BitVec.ofNat 64 (A / 2 ^ p)
  x8 : t.gpr .x8 = BitVec.ofNat 64 (k / 2 ^ p)
  x7 : t.gpr .x7 = BitVec.ofNat 64 w
  rep : ∃ V, Rep t.mem F S V W ∧ ∀ i < 16 * w, V (oBuf + i) = bufK V₀ k (i + A % 2 ^ p)

/-- The buffer's first `k` bytes, of `w` words, shifted left by `A ≤ k`
bytes, in `log2 k + 1` passes: pass `p` reads below `8 w + 2^p ≤ 8 w + k
≤ 16 w`, where the bytes from `k` are zero. -/
theorem passesK_ok {u : State} {F S : Addr} (L : Lay u F S) {V₀ : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V₀ W) {A k w : Nat} (hk0 : 0 < k) (hkw : k ≤ 8 * w) (hw : 8 * w ≤ 1024) (hA : A ≤ k)
    (hz : ∀ x, k ≤ x → x < 16 * w → V₀ (oBuf + x) = 0)
    (h17 : u.gpr .x17 = off S oBuf) (h14 : u.gpr .x14 = BitVec.ofNat 64 1) (h9 : u.gpr .x9 = BitVec.ofNat 64 A)
    (h8 : u.gpr .x8 = BitVec.ofNat 64 k) (h7 : u.gpr .x7 = BitVec.ofNat 64 w) :
    WP isa (.loop Impl.RsaPkcs1Enc.AArch64.Front.passK (.nonzero .x .x8)) u fun u' => Lay u' F S ∧
      Step F S [] u u' ∧ ∃ V, Rep u'.mem F S V W ∧ ∀ i < 16 * w, V (oBuf + i) = bufK V₀ k (i + A) := by
  have c3 : oBuf = 1024 := rfl
  obtain hk64 : k < 2 ^ 64 := by omega_arith
  obtain I0 : ShiftK u F S V₀ W A k w 0 u := ⟨L, Step.refl _ _ _ _, h17, h14,
    by rw [h9, Nat.pow_zero, Nat.div_one], by rw [h8, Nat.pow_zero, Nat.div_one], h7, V₀, R,
    fun i hi => by
      simp only [Nat.pow_zero, Nat.mod_one, Nat.add_zero, bufK]
      by_cases h : i < k
      · rw [ifp h]
      · rw [ifn h, hz i (by omega_arith) hi]⟩
  refine WP.mono (count_loop (n := k.log2 + 1) (by omega_arith) (ShiftK u F S V₀ W A k w) (fun p hp t I => ?_) I0)
    fun t I => ⟨I.L, I.st, ?_⟩
  · obtain ⟨V, Rt, hB⟩ := I.rep
    obtain hpk : 2 ^ p ≤ k :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega_arith)) (Nat.log2_self_le (by omega_arith))
    have hp0 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    refine WP.mono (passK_ok I.L Rt (a := A / 2 ^ p) (c := k / 2 ^ p) (d := 2 ^ p) (n := w)
      (by have := Nat.div_le_self A (2 ^ p); omega_arith) (by have := Nat.div_le_self k (2 ^ p); omega_arith)
      (by omega_arith) (by omega_arith) hw I.x17 I.x14 I.x9 I.x8 I.x7)
      fun t2 ⟨L2, S2, R2, x17, x14, x9, x8, x7⟩ => ⟨⟨L2, I.st.trans S2, x17,
        by rw [x14, Nat.pow_succ, Nat.mul_comm], by rw [x9, Nat.pow_succ, Nat.div_div_eq_div_mul],
        by rw [x8, Nat.pow_succ, Nat.div_div_eq_div_mul], x7, _, R2, fun i hi => ?_⟩, ?_⟩
    · simp only [selV]
      rw [Nat.mod_pow_succ]
      by_cases hi' : i < 8 * w
      · rw [ifp (show oBuf ≤ oBuf + i ∧ oBuf + i < oBuf + 8 * w by omega_arith)]
        rcases Nat.mod_two_eq_zero_or_one (A / 2 ^ p) with h0 | h1
        · rw [h0, show decide (0 = 1) = false from rfl]
          simp only [Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.add_zero]
          exact hB i hi
        · rw [h1, show decide (1 = 1) = true from rfl]
          simp only [ite_true, Nat.mul_one]
          rw [show oBuf + i + 2 ^ p = oBuf + (i + 2 ^ p) by omega_arith, hB (i + 2 ^ p) (by omega_arith)]
          congr 1; omega_arith
      · rw [ifn (show ¬ (oBuf ≤ oBuf + i ∧ oBuf + i < oBuf + 8 * w) by omega_arith), hB i hi, bufK, bufK,
          ifn (show ¬ (i + A % 2 ^ p < k) by omega_arith),
          ifn (show ¬ (i + (A % 2 ^ p + 2 ^ p * (A / 2 ^ p % 2)) < k) by omega_arith)]
    · rw [x8, Nat.div_div_eq_div_mul, ← Nat.pow_succ]; exact bits_ne (by omega_arith) hk64 hp
  · obtain ⟨V, Rt, hB⟩ := I.rep
    refine ⟨V, Rt, fun i hi => ?_⟩
    rw [hB i hi, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hA Nat.lt_log2_self)]

theorem getD_of {l : List Byte} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- The buffer, shifted left by the zeros before the message: the message,
then zeros. -/
theorem shift_val {s : State} {M : List Byte} {m0 : Mem} (hML : M.length ≤ kOf s)
    (hb : Spec.Rsa.bytesAt m0 (s.gpr .x0) (kOf s) = List.replicate (kOf s - M.length) 0 ++ M)
    {V₀ : Nat → Byte} (hV : ∀ x < zK s, V₀ (oBuf + x) =
      if x < kOf s then m0 (s.gpr .x0 + BitVec.ofNat 64 x) else 0)
    {i : Nat} (hi : i < kOf s) : bufK V₀ (kOf s) (i + (kOf s - M.length)) = (tgt s M).getD i 0 := by
  have key : ∀ j (hj : j < kOf s), m0 (s.gpr .x0 + BitVec.ofNat 64 j) =
      (List.replicate (kOf s - M.length) 0 ++ M)[j]'(by simp; omega_arith) := fun j hj => by
    have := congrArg (fun l : List Byte => l[j]?) hb
    simp only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hj, Option.map_some] at this
    rw [List.getElem?_eq_getElem (by simp; omega_arith)] at this
    exact Option.some.inj this
  obtain hkz : kOf s ≤ zK s := by show kOf s ≤ 16 * ((kOf s + 7) / 8); omega_arith
  obtain hsk : kOf s - M.length ≤ kOf s := Nat.sub_le _ _
  rw [getD_of (by simp; omega_arith), bufK]
  by_cases hiL : i < M.length
  · rw [ifp (by omega_arith : i + (kOf s - M.length) < kOf s), hV _ (by omega_arith),
      ifp (by omega_arith : i + (kOf s - M.length) < kOf s), key _ (by omega_arith),
      List.getElem_append_left hiL, List.getElem_append_right (by simp only [List.length_replicate]; omega_arith)]
    simp only [List.length_replicate, Nat.add_sub_cancel]
  · rw [List.getElem_append_right (by omega_arith), List.getElem_replicate, ifn (by omega_arith)]

theorem sh_ok {s v : State} (hp : FPre s) (h : St2 s v) :
    WP isa Impl.RsaPkcs1Enc.AArch64.Front.shift v (St3 s) := by
  obtain ⟨m0, R, M, V, W, hm, hV⟩ := h
  have hk := k_le hp
  have hML := hm.data.len
  have L := hm.L
  obtain h96 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  obtain h168 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  obtain h216 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 216) 8 := L.ld (d := 216) (by decide)
  have hs : v.mem.read (F s + BitVec.ofNat 64 96) 8 = S s := L.slot
  obtain rk := hm.rep.rd8 (d := 168) (k := 21) rfl (by decide) hm.w21
  obtain rml := hm.rep.rd8 (d := 216) (k := 27) rfl (by decide) hm.w27
  obtain hmlR : InRegions (v.rd ++ v.wr) (s.gpr .x2) 8 :=
    ⟨mlR s, by rw [hm.en.wr, entered_wr, hp.wr]; simp, Region.contains_self _ _⟩
  obtain hmlV : v.mem.read (s.gpr .x2) 8 = BitVec.ofNat 64 M.length := by rw [← rdW, hm.ml, hm.data.ml]
  unfold Impl.RsaPkcs1Enc.AArch64.Front.shift
  refine WP.seq (WP.mono (Q := fun (u : State) => u.mem = v.mem ∧ u.rd = v.rd ∧ u.wr = v.wr ∧ u.sp = v.sp ∧
      u.v = v.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = v.gpr r) ∧ u.gpr .x17 = off (S s) oBuf ∧
      u.gpr .x9 = BitVec.ofNat 64 (kOf s - M.length) ∧ u.gpr .x14 = BitVec.ofNat 64 1 ∧
      u.gpr .x8 = BitVec.ofNat 64 (kOf s) ∧ u.gpr .x7 = BitVec.ofNat 64 (wOf s)) ?_
    fun u ⟨um, urd, uwr, usp, uv, ucs, x17, x9, x14, x8, x7⟩ => ?_)
  · oaep_run [scr, VG.Impl.RsaOaep.AArch64.Mgf1.scr, VG.Impl.RsaOaep.AArch64.lay, sScr, sK, sMl, oBuf, h96, h168,
      h216, L.sp, hs, rk, rml, BitVec.add_zero, hmlR, hmlV, Offset.ofNat_sub_ofNat hML, words_bv hk, words_bv' hk,
      show BitVec.setWidth 64 (1 : BitVec 16) <<< 0 = BitVec.ofNat 64 1 by decide]
    oaep_fin
  obtain S1 : Step (F s) (S s) [] v u := Step.blk _ urd uwr usp uv ucs um
  have cB : oBuf = 1024 := rfl
  have ew : wOf s = (kOf s + 7) / 8 := rfl
  have ez : zK s = 16 * wOf s := rfl
  refine WP.mono (passesK_ok (L.congr usp uwr (by rw [um])) (um ▸ hm.rep) (A := kOf s - M.length) (k := kOf s)
    (w := wOf s) (by have := hp.kv.1; omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (fun x h1 h2 => by rw [hV x h2, ifn (by omega_arith)]) x17 x14 x9 x8 x7) fun w ⟨_, Sw, V', Rw, hB⟩ =>
    ⟨m0, R, M, V', W, hm.step hp nil_ws (S1.trans Sw) Rw fun _ _ => rfl, fun i hi => ?_⟩
  rw [hB i (by omega_arith)]
  exact shift_val hML hm.data.out hV hi

/-! ## The buffer back to `out` -/

theorem coutBody_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {o : Addr} {k j : Nat} (hj : j < k) (hk : k ≤ 1024) (hw : Covers [⟨o, k⟩] u.wr)
    (hnw : o.toNat + k ≤ 2 ^ 64) (ha : Apart F S ⟨o, k⟩) (h11 : u.gpr .x11 = off S (oBuf + j))
    (h12 : u.gpr .x12 = off o j) :
    WP isa (.block [.ldrb .x10 .x11 0, .strb .x10 .x12 0, .addImm .x .x11 .x11 1, .addImm .x .x12 .x12 1,
      .subImm .x .x13 .x13 1]) u fun u' => Lay u' F S ∧ Step F S [⟨o, k⟩] u u' ∧ Rep u'.mem F S V W ∧
      u'.mem = u.mem.write (off o j) 1 (V (oBuf + j)) ∧ u'.gpr .x11 = off S (oBuf + j + 1) ∧
      u'.gpr .x12 = off o (j + 1) ∧ u'.gpr .x13 = u.gpr .x13 - BitVec.ofNat 64 1 := by
  have cb : oBuf = 1024 := rfl
  have co : oRsa = 8192 := rfl
  have r1 : InRegions (u.rd ++ u.wr) (off S (oBuf + j)) 1 := L.sld (by omega_arith)
  have v1 : u.mem (off S (oBuf + j)) = V (oBuf + j) := R.scr _ (by omega_arith)
  have cj : Region.Contains ⟨o, k⟩ (off o j) 1 := Offset.contains_base o (by omega_arith) (by omega_arith)
  have w1 : InRegions u.wr (off o j) 1 := hw _ _ ⟨_, List.mem_singleton_self _, cj⟩
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off o j) 1 (V (oBuf + j)) ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧
      u'.gpr .x11 = off S (oBuf + j) + BitVec.ofNat 64 1 ∧ u'.gpr .x12 = off o j + BitVec.ofNat 64 1 ∧
      u'.gpr .x13 = u.gpr .x13 - BitVec.ofNat 64 1) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11, x12, x13⟩ => ?_
  · oaep_run [h11, h12, BitVec.add_zero, r1, w1, read_one, byte64, byte_rt64, v1]
    oaep_fin
  have hf : Frame [⟨o, k⟩] u.mem u'.mem := by
    rw [hm]; exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ cj
  have R' : Rep u'.mem F S V W := R.apart L.geo ha hf
  refine ⟨L.congr hsp hwr ?_, ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], hf.mono (by simp)⟩, R', hm,
    x11.trans (off_off S _ 1), x12.trans (off_off o j 1), x13⟩
  rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]

/-- The buffer's first `k` bytes (at `x11`, `x13` of them) to `o` (at `x12`). -/
theorem coutLoop_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {o : Addr} {k : Nat} (hk0 : 0 < k) (hk1 : k ≤ 1024) (hw : Covers [⟨o, k⟩] u.wr)
    (hnw : o.toNat + k ≤ 2 ^ 64) (ha : Apart F S ⟨o, k⟩) (h11 : u.gpr .x11 = off S oBuf) (h12 : u.gpr .x12 = o)
    (h13 : u.gpr .x13 = BitVec.ofNat 64 k) :
    WP isa copyLoop u fun u' => Lay u' F S ∧ Step F S [⟨o, k⟩] u u' ∧ Rep u'.mem F S V W ∧
      (∀ i < k, u'.mem (off o i) = V (oBuf + i)) := by
  refine WP.mono (count_loop hk0 (fun j w => Lay w F S ∧ Step F S [⟨o, k⟩] u w ∧ Rep w.mem F S V W ∧
      (∀ i < j, w.mem (off o i) = V (oBuf + i)) ∧ w.gpr .x11 = off S (oBuf + j) ∧ w.gpr .x12 = off o j ∧
      w.gpr .x13 = BitVec.ofNat 64 (k - j))
    (fun j hj w ⟨Lw, Sw, Rw, Ow, w11, w12, w13⟩ => ?_)
    ⟨L, Step.refl _ _ _ _, R, fun _ h => absurd h (Nat.not_lt_zero _), by rw [h11]; rfl,
      by rw [h12]; exact (BitVec.add_zero o).symm, h13⟩) fun w ⟨Lw, Sw, Rw, Ow, _⟩ => ⟨Lw, Sw, Rw, Ow⟩
  refine WP.mono (coutBody_ok Lw Rw hj hk1 (by rw [Sw.wr]; exact hw) hnw ha w11 w12)
    fun w' ⟨L', S', R', hm', x11', x12', x13'⟩ => ⟨⟨L', Sw.trans S', R', fun i hi => ?_, x11', x12', ?_⟩, ?_⟩
  · rw [hm', write1_apply]
    by_cases hij : i = j
    · subst hij; rw [ifp rfl]
    · rw [ifn (Offset.add_ofNat_ne o (by omega_arith) (by omega_arith) hij), Ow i (by omega_arith)]
  · rw [x13', w13, counter_step hj (by omega_arith)]
  · rw [x13', w13, counter_step hj (by omega_arith)]; exact counter_ne hj (by omega_arith)

theorem outK_eq {s : State} (hp : FPre s) : (⟨s.gpr .x0, kOf s⟩ : Region) = outR s := by
  rw [outR, hp.olk]

theorem cout_ok {s v : State} (hp : FPre s) (h : St3 s v) :
    WP isa Impl.RsaPkcs1Enc.AArch64.Front.copyOut v (St4 s) := by
  obtain ⟨m0, R, M, V, W, hm, hV⟩ := h
  have hk := k_le hp
  have hk1 := hp.kv.1
  have L := hm.L
  obtain h96 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  obtain h152 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 152) 8 := L.ld (d := 152) (by decide)
  obtain h168 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have hs : v.mem.read (F s + BitVec.ofNat 64 96) 8 = S s := L.slot
  obtain ro := hm.rep.rd8 (d := 152) (k := 19) rfl (by decide) hm.w19
  obtain rk := hm.rep.rd8 (d := 168) (k := 21) rfl (by decide) hm.w21
  unfold Impl.RsaPkcs1Enc.AArch64.Front.copyOut
  refine WP.seq (WP.mono (Q := fun (u : State) => u.mem = v.mem ∧ u.rd = v.rd ∧ u.wr = v.wr ∧ u.sp = v.sp ∧
      u.v = v.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = v.gpr r) ∧ u.gpr .x11 = off (S s) oBuf ∧
      u.gpr .x12 = s.gpr .x0 ∧ u.gpr .x13 = BitVec.ofNat 64 (kOf s)) ?_
    fun u ⟨um, urd, uwr, usp, uv, ucs, x11, x12, x13⟩ => ?_)
  · oaep_run [scr, VG.Impl.RsaOaep.AArch64.Mgf1.scr, VG.Impl.RsaOaep.AArch64.lay, sScr, sOut, sK, oBuf, h96, h152,
      h168, L.sp, hs, ro, rk]
    oaep_fin
  obtain S1 : Step (F s) (S s) [⟨s.gpr .x0, kOf s⟩] v u := Step.blk _ urd uwr usp uv ucs um
  have hbO := hp.bO
  have holk := hp.olk
  obtain ha : Apart (F s) (S s) ⟨s.gpr .x0, kOf s⟩ := by
    rw [outK_eq hp]
    exact ⟨(hp.kO.sub_left (frame_stk s)).symm, hp.dOS.sub_right (sR_sub hp), (hp.kO.sub_left (retR_stk s)).symm⟩
  refine WP.mono (coutLoop_ok (L.congr usp uwr (by rw [um])) (um ▸ hm.rep) (o := s.gpr .x0) (k := kOf s)
    (by omega_arith) hk (Covers.of_mem fun r hr => by
      rw [List.mem_singleton.mp hr, outK_eq hp, uwr, hm.en.wr, entered_wr, hp.wr]; simp)
    (by omega_arith) ha x11 x12 x13) fun w ⟨_, Sw, Rw, Ow⟩ => ?_
  refine ⟨m0, R, M, V, W, hm.step hp (ws := [⟨s.gpr .x0, kOf s⟩]) (fun r hr => by
    rw [List.mem_singleton.mp hr, outK_eq hp]) (S1.trans Sw) Rw fun _ _ => rfl, ?_⟩
  refine List.ext_getElem (by simp [Spec.Rsa.bytesAt, hm.data.len]) fun i h1 h2 => ?_
  have hi : i < kOf s := by simpa [Spec.Rsa.bytesAt] using h1
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  rw [show s.gpr .x0 + BitVec.ofNat 64 i = off (s.gpr .x0) i from rfl, Ow i hi, hV i hi, getD_of h2]

/-! ## The result, and the whole -/

/-- At the end of the body. -/
def Fin (s v : State) : Prop := En s v ∧ ∃ m0 R M, Data s m0 R M ∧
  v.mem.readW (s.gpr .x2) 64 = m0.readW (s.gpr .x2) 64 ∧ Spec.Rsa.bytesAt v.mem (s.gpr .x0) (kOf s) = tgt s M ∧
  v.gpr .x0 = R

theorem ret_ok {s v : State} (hp : FPre s) (h : St4 s v) :
    WP isa (.block Impl.RsaPkcs1Enc.AArch64.Front.ret) v (Fin s) := by
  obtain ⟨m0, R, M, V, W, hm, hb⟩ := h
  have L := hm.L
  obtain h224 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 224) 8 := L.ld (d := 224) (by decide)
  obtain rR := hm.rep.rd8 (d := 224) (k := 28) rfl (by decide) hm.w28
  refine WP.mono (Q := fun (u : State) => u.mem = v.mem ∧ u.rd = v.rd ∧ u.wr = v.wr ∧ u.sp = v.sp ∧
      u.v = v.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = v.gpr r) ∧ u.gpr .x0 = R) ?_
    fun u ⟨um, urd, uwr, usp, uv, ucs, x0⟩ => ?_
  · oaep_run [Impl.RsaPkcs1Enc.AArch64.Front.ret, sR, h224, L.sp, rR]
    oaep_fin
  obtain hm' := hm.step hp nil_ws (Step.blk _ urd uwr usp uv ucs um) (um ▸ hm.rep) fun _ _ => rfl
  exact ⟨hm'.en, m0, R, M, hm.data, hm'.ml, by rw [um]; exact hb, x0⟩

theorem tail_ok {s v : State} (hp : FPre s) (h : St0 s v) :
    WP isa Impl.RsaPkcs1Enc.AArch64.Front.tail v (Fin s) :=
  WP.seq (WP.mono (clear_ok hp h) fun _ h1 => WP.seq (WP.mono (cin_ok hp h1) fun _ h2 =>
    WP.seq (WP.mono (sh_ok hp h2) fun _ h3 => WP.seq (WP.mono (cout_ok hp h3) fun _ h4 => ret_ok hp h4))))

theorem body_ok {name : String} {callee : Prog isa}
    (hv : ∀ s, (DK 3488).pre s → ∃ t s', Exec isa callee s t s' ∧ abiPreserved s s' ∧ (DK 3488).post s s')
    (hd : 16 * callee.aarch64Depth ≤ 3488) {s : State} (h : (FK 3776).pre s) :
    WP isa (Impl.RsaPkcs1Enc.AArch64.Front.body name callee) (entered s) (Fin s) := by
  have hp := fpre_of h
  exact WP.seq (WP.mono (setup_ok hp) fun w hr => WP.seq (WP.mono (call_ok hv hd h hr) fun u hc =>
    WP.seq (WP.mono (after_ok hp hc) fun v h0 => tail_ok hp h0)))

theorem popped_gpr (t : State) (r : Reg) :
    (popped .x30 t).gpr r = if r = .x30 then t.mem.read t.sp 8 else t.gpr r := by
  show (t.write .x .x30 _).gpr r = _
  rw [RegUpd.gpr_write, BitVec.setWidth_eq]

theorem front_ok {name : String} {callee : Prog isa}
    (hv : ∀ s, (DK 3488).pre s → ∃ t s', Exec isa callee s t s' ∧ abiPreserved s s' ∧ (DK 3488).post s s')
    (hd : 16 * callee.aarch64Depth ≤ 3488) {s : State} (h : (FK 3776).pre s) :
    WP isa (Impl.RsaPkcs1Enc.AArch64.Front.code name callee) s fun s' => abiPreserved s s' ∧ (FK 3776).post s s' := by
  have hp := fpre_of h
  have hsp1 := hp.sp1
  have hBn := B_toNat hp
  refine WP.frameAlloc (by omega_arith) (by decide) ?_ ?_
  · rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; show 16 ≤ s.sp.toNat; omega_arith)]
    show 272 ≤ s.sp.toNat - 16
    omega_arith
  refine WP.mono (body_ok hv hd h) fun x ⟨hx, m0, R, M, hD, hml, hb, hx0⟩ mm uu fl => ?_
  have hsp' : (freed frameBytes x).sp = s.sp - 16 := by
    show x.sp + BitVec.ofNat 64 272 = _
    rw [hx.sp, F_off, lr_addr]
  obtain hS : Region.Sub (below s.sp (272 + 16)) (stkR s) := Offset.sub_below s.sp (by decide) (by decide)
  refine ⟨⟨fun r hr => ?_, ?_, fun r hr => hx.vs r hr⟩, ?_⟩
  · show (popped .x30 (freed frameBytes x)).gpr r = s.gpr r
    rw [popped_gpr]
    by_cases h30 : r = .x30
    · subst h30
      simp only [ite_true]
      rw [hsp', show (freed frameBytes x).mem = x.mem from rfl, ← rdW]
      exact hx.lr
    · simp only [h30, ite_false]; exact hx.cs r hr h30
  · show x.sp + BitVec.ofNat 64 272 + 16 = s.sp
    rw [hx.sp, F_off, BitVec.add_assoc, show BitVec.ofNat 64 (3488 + 272) + 16 = BitVec.ofNat 64 3776 from rfl, ← sp_B]
  · sig_post [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
      AArch64.abi, AArch64.argRegs, stackArgs17, List.append_eq,
      _root_.List.range, _root_.List.range.loop]
    have hbO := hp.bO
    have holk := hp.olk
    obtain hbm : Spec.Rsa.bytesAt mm (s.gpr .x0) (kOf s) = tgt s M := by
      rw [← hb]
      simp only [Spec.Rsa.bytesAt]
      exact List.map_congr_left fun i hi => fl.bytes (R := outR s) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.kO.sub_left hS).symm) (by dsimp only; omega_arith)
        (by show i < (s.gpr .x1).toNat; rw [holk]; exact List.mem_range.mp hi)
    obtain hmm : mm.readW (s.gpr .x2) 64 = m0.readW (s.gpr .x2) 64 := by
      rw [← hml]
      exact fl.readW (r := mlR s) (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.kM.sub_left hS).symm) (by decide)
    obtain hr0 : (popped .x30 (freed frameBytes x)).gpr .x0 = R := by
      rw [popped_gpr]; simp only [reduceCtorEq, ite_false]; exact hx0
    show Spec.RsaPkcs1Enc.writtenMsg mm (s.gpr .x0) (s.gpr .x2) (kOf s)
      ((popped .x30 (freed frameBytes x)).gpr .x0 |>.setWidth 32) (decOf s)
    rw [hr0]
    exact hD.fin mm hbm hmm

/-! ## Constant time: the public data -/

/-- The public data, by name. -/
structure PubEq (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  dit : s₁.dit = s₂.dit
  leak : List.map (fun x => BitVec.toNat x)
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat ++
        Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x5) (s₁.gpr .x6).toNat) ++
      Spec.Rsa.privatePrecomputedLeak s₁.mem (stackArg s₁ 15) (s₁.gpr .x4).toNat =
    List.map (fun x => BitVec.toNat x)
      (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x3) (s₂.gpr .x4).toNat ++
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x5) (s₂.gpr .x6).toNat) ++
      Spec.Rsa.privatePrecomputedLeak s₂.mem (stackArg s₂ 15) (s₂.gpr .x4).toNat
  g0 : s₁.gpr .x0 = s₂.gpr .x0
  g1 : s₁.gpr .x1 = s₂.gpr .x1
  g2 : s₁.gpr .x2 = s₂.gpr .x2
  g3 : s₁.gpr .x3 = s₂.gpr .x3
  g4 : s₁.gpr .x4 = s₂.gpr .x4
  g5 : s₁.gpr .x5 = s₂.gpr .x5
  g6 : s₁.gpr .x6 = s₂.gpr .x6
  g7 : s₁.gpr .x7 = s₂.gpr .x7
  a : ∀ j < 17, stackArg s₁ j = stackArg s₂ j

theorem pub_of {s₁ s₂ : State} (h : (FK 3776).pub s₁ s₂) : PubEq s₁ s₂ := by
  sig_pub_keep [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    AArch64.abi, AArch64.argRegs, stackArgs17, List.append_eq,
    _root_.List.range, _root_.List.range.loop] at h
  obtain ⟨hsp, hd, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14, a15, a16⟩ := h
  refine ⟨hsp, hd, hl, h0, h1, h2, h3, h4, h5, h6, h7, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => exact a0 | 1, _ => exact a1 | 2, _ => exact a2 | 3, _ => exact a3 | 4, _ => exact a4
  | 5, _ => exact a5 | 6, _ => exact a6 | 7, _ => exact a7 | 8, _ => exact a8 | 9, _ => exact a9
  | 10, _ => exact a10 | 11, _ => exact a11 | 12, _ => exact a12 | 13, _ => exact a13 | 14, _ => exact a14
  | 15, _ => exact a15 | 16, _ => exact a16 | _ + 17, hj => exact absurd hj (Nat.not_lt.mpr (Nat.le_add_left 17 _))

theorem PubEq.fEq {s₁ s₂ : State} (h : PubEq s₁ s₂) : F s₁ = F s₂ := by rw [F, F, h.sp]

theorem PubEq.rdEq {s₁ s₂ : State} (h : PubEq s₁ s₂) : rdC s₁ = rdC s₂ := by
  simp only [rdC, ro, h.g3, h.g4, h.g5, h.g6, h.g7, h.fEq, h.a 0 (by decide), h.a 1 (by decide), h.a 2 (by decide),
    h.a 3 (by decide), h.a 4 (by decide), h.a 5 (by decide), h.a 6 (by decide), h.a 7 (by decide),
    h.a 8 (by decide), h.a 9 (by decide), h.a 10 (by decide), h.a 11 (by decide), h.a 12 (by decide),
    h.a 15 (by decide), h.a 16 (by decide)]

theorem PubEq.wrEq {s₁ s₂ : State} (h : PubEq s₁ s₂) (h₁ : FPre s₁) (h₂ : FPre s₂) : s₁.wr = s₂.wr := by
  rw [h₁.wr, h₂.wr]
  simp only [outR, mlR, scrR, h.g0, h.g1, h.g2, h.a 13 (by decide), h.a 14 (by decide)]

/-- `pre`'s leaked words, apart from our stack. -/
theorem leak_eq {s : State} (hp : FPre s) {m : Mem} (hf : Frame [stkR s] s.mem m) :
    Spec.Rsa.privatePrecomputedLeak m (stackArg s 15) (s.gpr .x4).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 15) (s.gpr .x4).toNat := by
  have hle : Spec.Rsa.precomputedWords (s.gpr .x4).toNat ≤ (stackArg s 16).toNat := by
    rw [hp.prl]; unfold Spec.Rsa.privatePrecomputedWords; omega_arith
  have := hp.bPr
  unfold Spec.Rsa.privatePrecomputedLeak
  rw [words_eq hf (hp.kPr.sub_right (Region.sub_prefix (by omega_arith))) (by omega_arith)]

theorem call_pub {s₁ s₂ w₁ w₂ : State} (h₁ : FPre s₁) (h₂ : FPre s₂) (hp : PubEq s₁ s₂) (r₁ : Ready s₁ w₁)
    (r₂ : Ready s₂ w₂) : (DK 3488).pub (cEntry s₁ w₁) (cEntry s₂ w₂) := by
  sig_pub_keep [Proof.RsaPkcs1Enc.decryptPrecomputedBodyContract, Proof.RsaPkcs1Enc.decryptPrecomputedBodySig,
    Proof.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs, stackArgs17, List.append_eq,
    _root_.List.range, _root_.List.range.loop]
  have := h₁.kv.2
  have := h₂.kv.2
  have := h₁.bN
  have := h₂.bN
  have := h₁.bE
  have := h₂.bE
  simp only [r₁.sp, r₂.sp, r₁.dit, r₂.dit, r₁.gpr .x0 (by decide) (by decide), r₁.gpr .x1 (by decide) (by decide),
    r₁.gpr .x2 (by decide) (by decide), r₁.gpr .x3 (by decide) (by decide), r₁.gpr .x4 (by decide) (by decide),
    r₁.gpr .x5 (by decide) (by decide), r₁.gpr .x6 (by decide) (by decide), r₁.gpr .x7 (by decide) (by decide),
    r₂.gpr .x0 (by decide) (by decide), r₂.gpr .x1 (by decide) (by decide),
    r₂.gpr .x2 (by decide) (by decide), r₂.gpr .x3 (by decide) (by decide), r₂.gpr .x4 (by decide) (by decide),
    r₂.gpr .x5 (by decide) (by decide), r₂.gpr .x6 (by decide) (by decide), r₂.gpr .x7 (by decide) (by decide),
    ce_arg r₁ (j := 15) (by decide), ce_arg r₂ (j := 15) (by decide),
    bytes_eq r₁.fr h₁.kN (by omega_arith), bytes_eq r₂.fr h₂.kN (by omega_arith),
    bytes_eq r₁.fr h₁.kE (by omega_arith), bytes_eq r₂.fr h₂.kE (by omega_arith),
    leak_eq h₁ r₁.fr, leak_eq h₂ r₂.fr]
  refine ⟨hp.fEq, hp.dit, hp.leak, hp.g0, hp.g1, hp.g2, hp.g3, hp.g4, hp.g5, hp.g6, hp.g7, ?_⟩
  simp only [ce_arg r₁ (j := 0) (by decide), ce_arg r₂ (j := 0) (by decide), ce_arg r₁ (j := 1) (by decide),
    ce_arg r₂ (j := 1) (by decide), ce_arg r₁ (j := 2) (by decide), ce_arg r₂ (j := 2) (by decide),
    ce_arg r₁ (j := 3) (by decide), ce_arg r₂ (j := 3) (by decide), ce_arg r₁ (j := 4) (by decide),
    ce_arg r₂ (j := 4) (by decide), ce_arg r₁ (j := 5) (by decide), ce_arg r₂ (j := 5) (by decide),
    ce_arg r₁ (j := 6) (by decide), ce_arg r₂ (j := 6) (by decide), ce_arg r₁ (j := 7) (by decide),
    ce_arg r₂ (j := 7) (by decide), ce_arg r₁ (j := 8) (by decide), ce_arg r₂ (j := 8) (by decide),
    ce_arg r₁ (j := 9) (by decide), ce_arg r₂ (j := 9) (by decide), ce_arg r₁ (j := 10) (by decide),
    ce_arg r₂ (j := 10) (by decide), ce_arg r₁ (j := 11) (by decide), ce_arg r₂ (j := 11) (by decide),
    ce_arg r₁ (j := 12) (by decide), ce_arg r₂ (j := 12) (by decide), ce_arg r₁ (j := 13) (by decide),
    ce_arg r₂ (j := 13) (by decide), ce_arg r₁ (j := 14) (by decide), ce_arg r₂ (j := 14) (by decide),
    ce_arg r₁ (j := 16) (by decide), ce_arg r₂ (j := 16) (by decide)]
  exact ⟨hp.a 0 (by decide), hp.a 1 (by decide), hp.a 2 (by decide), hp.a 3 (by decide), hp.a 4 (by decide),
    hp.a 5 (by decide), hp.a 6 (by decide), hp.a 7 (by decide), hp.a 8 (by decide), hp.a 9 (by decide),
    hp.a 10 (by decide), hp.a 11 (by decide), hp.a 12 (by decide), hp.a 13 (by decide), hp.a 14 (by decide),
    hp.a 15 (by decide), hp.a 16 (by decide)⟩

/-! ## Constant time: two runs -/

/-- Two runs from states of the contract with the same public data, each
`G` of its own. -/
def Rel (G : State → State → Prop) (a b : State) : Prop :=
  ∃ s₁ s₂, (FK 3776).pre s₁ ∧ (FK 3776).pre s₂ ∧ (FK 3776).pub s₁ s₂ ∧ G s₁ a ∧ G s₂ b

/-- Code with the same trace in two such runs, which leaves each `G'`. -/
theorem rel_step {G G' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Rel G) c fun _ _ => True)
    (hw : ∀ s v, (FK 3776).pre s → G s v → WP isa c v (G' s)) : RelCT isa (Rel G) c (Rel G') := by
  intro a b ta tb a' b' hr e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨s₁, s₂, h₁, h₂, hp, g₁, g₂⟩ := hr
  obtain ⟨_, u₁, y₁, z₁⟩ := hw s₁ a h₁ g₁
  obtain ⟨_, u₂, y₂, z₂⟩ := hw s₂ b h₂ g₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ y₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ y₂
  exact ⟨ht, s₁, s₂, h₁, h₂, hp, z₁, z₂⟩

/-- Code the taint analysis checks from `sp` and the registers `rs`, which
hold public values `pin s` in each run. -/
theorem rel_taint {G : State → State → Prop} {c : Prog isa} (rs : List Reg) (pin : State → Reg → BitVec 64)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hsp : ∀ s v, G s v → v.sp = F s) (hpin : ∀ s v, G s v → ∀ r ∈ rs, v.gpr r = pin s r)
    (hpe : ∀ s₁ s₂, PubEq s₁ s₂ → ∀ r ∈ rs, pin s₁ r = pin s₂ r) : RelCT isa (Rel G) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun a b ⟨s₁, s₂, _, _, hp, g₁, g₂⟩ => by
    have hq := pub_of hp
    exact ⟨by rw [hsp _ _ g₁, hsp _ _ g₂, hq.fEq], fun r hr => by
      rw [hpin _ _ g₁ r (Taint.mem_ofRegs.mp hr), hpin _ _ g₂ r (Taint.mem_ofRegs.mp hr),
        hpe _ _ hq r (Taint.mem_ofRegs.mp hr)]⟩) h

/-- A head `c₁` the taint analysis checks from `sp`, which sets the registers
`rs` to public values `pin s`, then `c₂`, checked from them. -/
theorem rel_seq_tr {G : State → State → Prop} {c₁ c₂ : Prog isa} (rs : List Reg) (pin : State → Reg → BitVec 64)
    {h₁ h₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs []) c₁ h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs rs) c₂ h₂).isSome = true) (hsp : ∀ s v, G s v → v.sp = F s)
    (hA : ∀ s v, (FK 3776).pre s → G s v → WP isa c₁ v fun u => u.sp = v.sp ∧ ∀ r ∈ rs, u.gpr r = pin s r)
    (hpe : ∀ s₁ s₂, PubEq s₁ s₂ → ∀ r ∈ rs, pin s₁ r = pin s₂ r) :
    RelCT isa (Rel G) (.seq c₁ c₂) fun _ _ => True := by
  have h1 : RelCT isa (Rel G) c₁ (Rel fun s u => u.sp = F s ∧ ∀ r ∈ rs, u.gpr r = pin s r) :=
    rel_step (rel_taint [] pin t₁ hsp (fun _ _ _ _ h => absurd h List.not_mem_nil)
      (fun _ _ _ _ h => absurd h List.not_mem_nil))
      fun s v hs hg => WP.mono (hA s v hs hg) fun u ⟨hu, hr⟩ => ⟨hu.trans (hsp s v hg), hr⟩
  exact h1.seq (rel_taint rs pin t₂ (fun _ _ h => h.1) (fun _ _ h => h.2) hpe)

/-! ## Constant time: the blocks -/

theorem setup_taint : ∃ hc, (taint.check (Taint.ofRegs []) (.block Impl.RsaPkcs1Enc.AArch64.Front.setup) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem after_taint : ∃ hc, (taint.check (Taint.ofRegs []) (.block Impl.RsaPkcs1Enc.AArch64.Front.after) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## Constant time: the pieces after the call -/

/-- The pins of the pieces' heads: `scratch + oBuf`, `out`, `k`, `msg_len`. -/
abbrev pinClr (s : State) (r : Reg) : BitVec 64 :=
  ([(Reg.x11, off (S s) oBuf), (.x12, BitVec.ofNat 64 (kOf s))].lookup r).getD 0
abbrev pinCin (s : State) (r : Reg) : BitVec 64 :=
  ([(Reg.x11, s.gpr .x0), (.x12, off (S s) oBuf), (.x13, BitVec.ofNat 64 (kOf s))].lookup r).getD 0
abbrev pinSh (s : State) (r : Reg) : BitVec 64 :=
  ([(Reg.x17, off (S s) oBuf), (.x10, s.gpr .x2), (.x8, BitVec.ofNat 64 (kOf s)),
    (.x7, BitVec.ofNat 64 (kOf s))].lookup r).getD 0
abbrev pinCout (s : State) (r : Reg) : BitVec 64 :=
  ([(Reg.x11, off (S s) oBuf), (.x12, s.gpr .x0), (.x13, BitVec.ofNat 64 (kOf s))].lookup r).getD 0

theorem pin_eq {s₁ s₂ : State} (h : PubEq s₁ s₂) :
    pinClr s₁ = pinClr s₂ ∧ pinCin s₁ = pinCin s₂ ∧ pinSh s₁ = pinSh s₂ ∧ pinCout s₁ = pinCout s₂ := by
  unfold pinClr pinCin pinSh pinCout S kOf
  rw [h.a 13 (by decide), h.g0, h.g2, h.g4]
  exact ⟨rfl, rfl, rfl, rfl⟩

section
variable {s v : State} {m0 : Mem} {R : BitVec 64} {M : List Byte} {V : Nat → Byte} {W : Nat → BitVec 64}
  (hm : Mid s v m0 R M V W)
include hm

theorem clrA_pin :
    WP isa (.block (scr .x11 oBuf ++ ([.ldrSp .x12 sK] : List Instr))) v fun u =>
      u.sp = v.sp ∧ ∀ r ∈ [Reg.x11, .x12], u.gpr r = pinClr s r := by
  have L := hm.L
  obtain h96 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  obtain h168 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have hs : v.mem.read (F s + BitVec.ofNat 64 96) 8 = S s := L.slot
  obtain rk := hm.rep.rd8 (d := 168) (k := 21) rfl (by decide) hm.w21
  refine WP.mono (Q := fun (u : State) => u.sp = v.sp ∧ u.gpr .x11 = off (S s) oBuf ∧
      u.gpr .x12 = BitVec.ofNat 64 (kOf s)) ?_
    fun u ⟨hs, x11, x12⟩ => pin_list [(Reg.x11, off (S s) oBuf), (.x12, BitVec.ofNat 64 (kOf s))] hs (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl) <;> with_reducible assumption)
  oaep_run [scr, VG.Impl.RsaOaep.AArch64.Mgf1.scr, VG.Impl.RsaOaep.AArch64.lay, sScr, sK, oBuf, h96, h168, L.sp,
    hs, rk]

theorem cinA_pin :
    WP isa (.block (([.ldrSp .x11 sOut] : List Instr) ++ scr .x12 oBuf ++ ([.ldrSp .x13 sK] : List Instr))) v
      fun u => u.sp = v.sp ∧
      ∀ r ∈ [Reg.x11, .x12, .x13], u.gpr r = pinCin s r := by
  have L := hm.L
  obtain h96 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  obtain h152 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 152) 8 := L.ld (d := 152) (by decide)
  obtain h168 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have hs : v.mem.read (F s + BitVec.ofNat 64 96) 8 = S s := L.slot
  obtain ro := hm.rep.rd8 (d := 152) (k := 19) rfl (by decide) hm.w19
  obtain rk := hm.rep.rd8 (d := 168) (k := 21) rfl (by decide) hm.w21
  refine WP.mono (Q := fun (u : State) => u.sp = v.sp ∧ u.gpr .x11 = s.gpr .x0 ∧ u.gpr .x12 = off (S s) oBuf ∧
      u.gpr .x13 = BitVec.ofNat 64 (kOf s)) ?_
    fun u ⟨hs, x11, x12, x13⟩ => pin_list [(Reg.x11, s.gpr .x0), (.x12, off (S s) oBuf),
      (.x13, BitVec.ofNat 64 (kOf s))] hs (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl | rfl) <;> with_reducible assumption)
  oaep_run [scr, VG.Impl.RsaOaep.AArch64.Mgf1.scr, VG.Impl.RsaOaep.AArch64.lay, sScr, sOut, sK, oBuf, h96, h152,
    h168, L.sp, hs, ro, rk]

theorem shA_pin :
    WP isa (.block (scr .x17 oBuf ++ ([.ldrSp .x9 sK, .ldrSp .x10 sMl, .ldrSp .x8 sK, .ldrSp .x7 sK] : List Instr)))
      v fun u => u.sp = v.sp ∧ ∀ r ∈ [Reg.x17, .x10, .x8, .x7], u.gpr r = pinSh s r := by
  have L := hm.L
  obtain h96 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  obtain h168 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  obtain h216 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 216) 8 := L.ld (d := 216) (by decide)
  have hs : v.mem.read (F s + BitVec.ofNat 64 96) 8 = S s := L.slot
  obtain rk := hm.rep.rd8 (d := 168) (k := 21) rfl (by decide) hm.w21
  obtain rml := hm.rep.rd8 (d := 216) (k := 27) rfl (by decide) hm.w27
  refine WP.mono (Q := fun (u : State) => u.sp = v.sp ∧ u.gpr .x17 = off (S s) oBuf ∧ u.gpr .x10 = s.gpr .x2 ∧
      u.gpr .x8 = BitVec.ofNat 64 (kOf s) ∧ u.gpr .x7 = BitVec.ofNat 64 (kOf s)) ?_
    fun u ⟨hs, x17, x10, x8, x7⟩ => pin_list [(Reg.x17, off (S s) oBuf), (.x10, s.gpr .x2),
      (.x8, BitVec.ofNat 64 (kOf s)), (.x7, BitVec.ofNat 64 (kOf s))] hs (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl) <;> with_reducible assumption)
  oaep_run [scr, VG.Impl.RsaOaep.AArch64.Mgf1.scr, VG.Impl.RsaOaep.AArch64.lay, sScr, sK, sMl, oBuf, h96, h168,
    h216, L.sp, hs, rk, rml]

theorem coutA_pin :
    WP isa (.block (scr .x11 oBuf ++ ([.ldrSp .x12 sOut, .ldrSp .x13 sK] : List Instr))) v fun u => u.sp = v.sp ∧
      ∀ r ∈ [Reg.x11, .x12, .x13], u.gpr r = pinCout s r := by
  have L := hm.L
  obtain h96 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 96) 8 := L.ld (d := 96) (by decide)
  obtain h152 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 152) 8 := L.ld (d := 152) (by decide)
  obtain h168 : InRegions (v.rd ++ v.wr) (F s + BitVec.ofNat 64 168) 8 := L.ld (d := 168) (by decide)
  have hs : v.mem.read (F s + BitVec.ofNat 64 96) 8 = S s := L.slot
  obtain ro := hm.rep.rd8 (d := 152) (k := 19) rfl (by decide) hm.w19
  obtain rk := hm.rep.rd8 (d := 168) (k := 21) rfl (by decide) hm.w21
  refine WP.mono (Q := fun (u : State) => u.sp = v.sp ∧ u.gpr .x11 = off (S s) oBuf ∧ u.gpr .x12 = s.gpr .x0 ∧
      u.gpr .x13 = BitVec.ofNat 64 (kOf s)) ?_
    fun u ⟨hs, x11, x12, x13⟩ => pin_list [(Reg.x11, off (S s) oBuf), (.x12, s.gpr .x0),
      (.x13, BitVec.ofNat 64 (kOf s))] hs (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl | rfl) <;> with_reducible assumption)
  oaep_run [scr, VG.Impl.RsaOaep.AArch64.Mgf1.scr, VG.Impl.RsaOaep.AArch64.lay, sScr, sOut, sK, oBuf, h96, h152,
    h168, L.sp, hs, ro, rk]

end

theorem clr_ct : RelCT isa (Rel St0) Impl.RsaPkcs1Enc.AArch64.Front.clearK (Rel St1) := by
  refine rel_step ?_ fun s v h hv => clear_ok (fpre_of h) hv
  show RelCT isa _ (.seq (.block ((scr .x11 oBuf ++ [.ldrSp .x12 sK]) ++
    [.addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3, .add .x .x12 .x12 .x12, .movz .x .x13 0 0]))
    (.loop (.block [.str .x .x13 .x11 0, .addImm .x .x11 .x11 8, .subImm .x .x12 .x12 1]) (.nonzero .x .x12))) _
  exact VG.Proof.RsaOaep.AArch64.RelCT.seq_block_append (rel_seq_tr [.x11, .x12] pinClr (by taint_decide)
    (by taint_decide) (fun _ _ ⟨_, _, _, _, _, hm, _⟩ => hm.en.sp) (fun _ _ _ ⟨_, _, _, _, _, hm, _⟩ => clrA_pin hm)
    fun _ _ h => by rw [(pin_eq h).1]; exact fun _ _ => rfl)

theorem cin_ct : RelCT isa (Rel St1) Impl.RsaPkcs1Enc.AArch64.Front.copyIn (Rel St2) := by
  refine rel_step ?_ fun s v h hv => cin_ok (fpre_of h) hv
  unfold Impl.RsaPkcs1Enc.AArch64.Front.copyIn
  exact rel_seq_tr [.x11, .x12, .x13] pinCin (by taint_decide) (by taint_decide)
    (fun _ _ ⟨_, _, _, _, _, hm, _⟩ => hm.en.sp) (fun _ _ _ ⟨_, _, _, _, _, hm, _⟩ => cinA_pin hm)
    fun _ _ h => by rw [(pin_eq h).2.1]; exact fun _ _ => rfl

theorem sh_ct : RelCT isa (Rel St2) Impl.RsaPkcs1Enc.AArch64.Front.shift (Rel St3) := by
  refine rel_step ?_ fun s v h hv => sh_ok (fpre_of h) hv
  show RelCT isa _ (.seq (.block ((scr .x17 oBuf ++ [.ldrSp .x9 sK, .ldrSp .x10 sMl, .ldrSp .x8 sK, .ldrSp .x7 sK]) ++
    [.ldr .x .x10 .x10 0, .sub .x .x9 .x9 .x10, .movz .x .x14 1 0, .addImm .x .x7 .x7 7, .lsr .x .x7 .x7 3]))
    (.loop Impl.RsaPkcs1Enc.AArch64.Front.passK (.nonzero .x .x8))) _
  exact VG.Proof.RsaOaep.AArch64.RelCT.seq_block_append (rel_seq_tr [.x17, .x10, .x8, .x7] pinSh (by taint_decide)
    (by taint_decide) (fun _ _ ⟨_, _, _, _, _, hm, _⟩ => hm.en.sp) (fun _ _ _ ⟨_, _, _, _, _, hm, _⟩ => shA_pin hm)
    fun _ _ h => by rw [(pin_eq h).2.2.1]; exact fun _ _ => rfl)

theorem cout_ct : RelCT isa (Rel St3) Impl.RsaPkcs1Enc.AArch64.Front.copyOut (Rel St4) := by
  refine rel_step ?_ fun s v h hv => cout_ok (fpre_of h) hv
  unfold Impl.RsaPkcs1Enc.AArch64.Front.copyOut
  exact rel_seq_tr [.x11, .x12, .x13] pinCout (by taint_decide) (by taint_decide)
    (fun _ _ ⟨_, _, _, _, _, hm, _⟩ => hm.en.sp) (fun _ _ _ ⟨_, _, _, _, _, hm, _⟩ => coutA_pin hm)
    fun _ _ h => by rw [(pin_eq h).2.2.2]; exact fun _ _ => rfl

theorem ret_ct : RelCT isa (Rel St4) (.block Impl.RsaPkcs1Enc.AArch64.Front.ret) (Rel Fin) :=
  rel_step (rel_taint [] pinClr (by taint_decide) (fun _ _ ⟨_, _, _, _, _, hm, _⟩ => hm.en.sp)
    (fun _ _ _ _ h => absurd h List.not_mem_nil) (fun _ _ _ _ h => absurd h List.not_mem_nil))
    fun s v h hv => ret_ok (fpre_of h) hv

theorem tail_ct : RelCT isa (Rel St0) Impl.RsaPkcs1Enc.AArch64.Front.tail (Rel Fin) :=
  clr_ct.seq (cin_ct.seq (sh_ct.seq (cout_ct.seq ret_ct)))

/-! ## Constant time: the call, and the whole -/

theorem call_ct {name : String} {callee : Prog isa} (hv : Verified AArch64.target callee (DK 3488)) :
    RelCT isa (Rel Ready) (.call name callee) fun _ _ => True := by
  refine (RelCT.exists_ (P := fun (s₀ : State) a b => ∃ s₂, (FK 3776).pre s₀ ∧ (FK 3776).pre s₂ ∧
      (FK 3776).pub s₀ s₂ ∧ Ready s₀ a ∧ Ready s₂ b) fun s₀ => ?_).mono
    (fun a b ⟨s₁, s₂, h₁, h₂, hp, r₁, r₂⟩ => ⟨s₁, s₂, h₁, h₂, hp, r₁, r₂⟩) fun _ _ h => h
  refine RelCT.call hv.1 hv.2.1 (rdC s₀) s₀.wr fun a b ⟨s₂, h₁, h₂, hp, r₁, r₂⟩ => ?_
  have q := pub_of hp
  have p₁ := fpre_of h₁
  have p₂ := fpre_of h₂
  obtain e : b.callEntry.withRegions (rdC s₀) s₀.wr = cEntry s₂ b := by rw [q.rdEq, q.wrEq p₁ p₂]
  refine ⟨call_pre h₁ r₁, by rw [e]; exact call_pre h₂ r₂, by rw [e]; exact call_pub p₁ p₂ q r₁ r₂,
    (call_covers p₁ r₁).1, (call_covers p₁ r₁).2, ?_, ?_⟩
  · rw [q.rdEq, q.wrEq p₁ p₂]; exact (call_covers p₂ r₂).1
  · rw [q.wrEq p₁ p₂]; exact (call_covers p₂ r₂).2

theorem front_ct {name : String} {callee : Prog isa} (hv : Verified AArch64.target callee (DK 3488))
    (hd : 16 * callee.aarch64Depth ≤ 3488) :
    ConstantTime isa (FK 3776).pre (FK 3776).pub (Impl.RsaPkcs1Enc.AArch64.Front.code name callee) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => (pub_of h.2.2).sp)
    (RelCT.alloc (R := fun _ _ => True) ?_))
  refine RelCT.mono (P := Rel fun s v => v = entered s) (Q := Rel Fin) ?_
    (fun a b ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, e₁, e₂⟩, ea, eb⟩ => ⟨s₁, s₂, h₁, h₂, hp, by rw [ea, e₁], by rw [eb, e₂]⟩)
    fun _ _ _ => trivial
  show RelCT isa _ (.seq (.block Impl.RsaPkcs1Enc.AArch64.Front.setup) (.seq (.call name callee)
    (.seq (.block Impl.RsaPkcs1Enc.AArch64.Front.after) Impl.RsaPkcs1Enc.AArch64.Front.tail))) _
  obtain ⟨_, ts⟩ := setup_taint
  obtain ⟨_, ta⟩ := after_taint
  exact (rel_step (rel_taint [] pinClr ts (fun s v h => by rw [h]; exact entered_sp s)
      (fun _ _ _ _ h => absurd h List.not_mem_nil) (fun _ _ _ _ h => absurd h List.not_mem_nil))
      fun s v h hv => hv ▸ setup_ok (fpre_of h)).seq
    ((rel_step (call_ct hv) fun s v h hv' => call_ok hv.1 hd h hv').seq
    ((rel_step (rel_taint [] pinClr ta (fun _ _ h => h.sp)
      (fun _ _ _ _ h => absurd h List.not_mem_nil) (fun _ _ _ _ h => absurd h List.not_mem_nil))
      fun s v h hv' => after_ok (fpre_of h) hv').seq tail_ct))

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_decrypt_precomputed`, calling any implementation
`callee` of `vg_rsa_pkcs1_decrypt_precomputed_body` verified with 3488 bytes of
stack, which its frames fit in. -/
theorem front_verified {name : String} {callee : Prog isa} (hv : Verified AArch64.target callee (DK 3488))
    (hd : 16 * callee.aarch64Depth ≤ 3488) (hsat : ∃ s, (FK 3776).pre s) :
    Verified AArch64.target (Impl.RsaPkcs1Enc.AArch64.Front.code name callee) (FK 3776) :=
  ⟨fun _ h => front_ok hv.1 hd h, front_ct hv hd, hsat⟩

/-- How deeply its frames nest: its own two, over the callee's. -/
theorem front_depth (name : String) (callee : Prog isa) :
    (Impl.RsaPkcs1Enc.AArch64.Front.code name callee).aarch64Depth = callee.aarch64Depth + 18 := by
  simp only [Impl.RsaPkcs1Enc.AArch64.Front.code, Impl.RsaPkcs1Enc.AArch64.Front.body,
    Impl.RsaPkcs1Enc.AArch64.Front.tail, Impl.RsaPkcs1Enc.AArch64.Front.copyIn,
    Impl.RsaPkcs1Enc.AArch64.Front.shift, Impl.RsaPkcs1Enc.AArch64.Front.copyOut, VG.Impl.RsaOaep.AArch64.Mgf1.seqs,
    Impl.RsaPkcs1Enc.AArch64.Front.clearK, Impl.RsaPkcs1Enc.AArch64.Front.passK, copyLoop, Code.aarch64Depth, Instr.frameUnits, frameBytes, Nat.zero_max, Nat.max_zero,
    Nat.reduceDiv, Nat.add_assoc, Nat.reduceAdd]

end VG.Proof.RsaPkcs1Enc.AArch64.Front
